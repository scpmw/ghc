
// For reading DWARF debug data of our own executable as well as all
// dynamically linked-in libraries. Uses libdwarf, this is
// roughly adapted from their simplereader.c example.

#ifdef USE_DWARF /* ugly? */

#include "Rts.h"
#include "RtsUtils.h"

#include "Dwarf.h"
#include "Trace.h"

#include "dwarf.h"
#include "libdwarf.h"
#include "gelf.h"

#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <stdio.h>
#include <fcntl.h>
#include <string.h>


// As far as I know, there are two ways for getting at the program's
// memory map on Linux:
//
//  1. Read /proc/self/maps
//
//  2. Use dl_iterate_phdr
//
// I am a bit unsure what the "preferred" method is here, given that
// both aren't portable. For now I use the /proc/self/maps method
// by default, as it also solves the problem of where to get the
// location of the executable from.

// #define USE_DL_ITERATE_PHDR


#ifdef USE_DL_ITERATE_PHDR
#define _GNU_SOURCE
#include <link.h>
#endif //USE_DL_ITERATE_PHDR

// Global compilation unit list
DwarfUnit *dwarf_units = 0;

// Debugging data
size_t dwarf_ghc_debug_data_size = 0;
void *dwarf_ghc_debug_data = 0;

#define GHC_DEBUG_DATA_SECTION ".debug_ghc"

#define GHC_DEBUG_NO_ID ((StgWord16) 0xffff)

struct seg_space_
{
    void *base;         // Add this to position in file to get virtual address
    void *start, *end;  // Limits of segment address space
    size_t file_offset; // Where in the file the mapping begins
    struct seg_space_ *next;
};
typedef struct seg_space_ seg_space;

static void dwarf_get_code_bases(Elf *elf, seg_space *seg);
static void dwarf_load_ghc_debug_data(Elf *elf);
static void dwarf_load_symbols(char *file, Elf *elf, seg_space *seg);

static void dwarf_load_file(char *module_path, seg_space *seg);
static void dwarf_load_dies(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, seg_space *seg);
static void dwarf_load_proc_die(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, seg_space *seg);
static void dwarf_load_block_die(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, seg_space *seg);
static char *dwarf_findname(Dwarf_Die die);

static DwarfUnit *dwarf_new_unit(char *name, char *comp_dir);
static DwarfProc *dwarf_new_proc(DwarfUnit *unit, char *name, Dwarf_Addr low_pc, Dwarf_Addr high_pc,
                                 DwarfSource source, seg_space *seg);

StgWord16 word16LE(StgWord8 *p);

void dwarf_associate_debug_data(StgBool trace);

#ifndef USE_DL_ITERATE_PHDR

void dwarf_load()
{
	// Clear previous data, if any
	dwarf_free();

	// Initialize ELF library
	if (elf_version(EV_CURRENT) == EV_NONE) {
		errorBelch("libelf version too old!");
		return;
	}

	// Open our process' memory map
	FILE *map_file = fopen("/proc/self/maps", "r");
	if (!map_file) {
		sysErrorBelch("Could not read /proc/self/map!");
		return;
	}

	// Accumulated segments for the same file. We assume that all
	// segments for a file are going to be listed together, so we
	// don't have to maintain a real map.
	seg_space *segs = NULL;
	char *cur_module = NULL;

	// Read out mappings
	char line[1025];
	while (!feof(map_file)) {

		// Read a line
		void *seg_start = 0, *seg_end = 0;
		char exec_perm = '-';
		char module_path[255+1] = "";
		unsigned int offset;
		if (!fgets(line, 1024, map_file))
			break;
		if (!sscanf(line, "%p-%p %*c%*c%c%*c %x %*x:%*x %*d %255s",
		            &seg_start, &seg_end, &exec_perm, &offset, module_path) > 0)
			break;

		// Different module? Load its segments
		if (segs && strcmp(cur_module, module_path)) {
			dwarf_load_file(cur_module, segs);
			free(cur_module); cur_module = NULL;
			seg_space *seg;
			while ((seg = segs)) {
				segs = seg->next;
				stgFree(seg);
			}
		}

		// Add to list, if it is an executable section
		if (exec_perm == 'x' && module_path[0] && module_path[0] != '[') {
			if (!cur_module) cur_module = strdup(module_path);
			seg_space *seg = (seg_space *)stgMallocBytes(sizeof(seg_space), "dwarf_new_seg_space");
			seg->base = NULL; // Might get corrected later
			seg->start = seg_start;
			seg->end = seg_end;
			seg->file_offset = offset;
			seg->next = segs;
			segs = seg;
		}

	}

	// Process any remaining segments
	if (segs) {
		dwarf_load_file(cur_module, segs);
		free(cur_module); cur_module = NULL;
		seg_space *seg;
		while ((seg = segs)) {
			segs = seg->next;
			stgFree(seg);
		}
	}

	fclose(map_file);
}

#else // USE_DL_ITERATE_PHDR

int dwarf_load_by_phdr(struct dl_phdr_info *info, size_t size, void *data);

void dwarf_load()
{
	// Initialize ELF library
	if (elf_version(EV_CURRENT) == EV_NONE) {
		errorBelch("libelf version too old!");
		return;
	}

	// Get own executable path
	char exe_path[1024+1];
	int len = readlink("/proc/self/exe", exe_path, sizeof(exe_path)-1);
	if (len < 0) {
		sysErrorBelch("Could not read /proc/self/exe!");
		return;
	}
	exe_path[len] = '\0';

	// Iterate over our memory sections
	struct dwarf_state state = { exe_path };
	dl_iterate_phdr(&dwarf_load_by_phdr, &state);

}

int dwarf_load_by_phdr(struct dl_phdr_info *info, size_t size, void *data)
{
	struct dwarf_state *state = (struct dwarf_state *)data;

	// Find range of executable code
	void *code_start = 0, *code_end = 0;
	void *code_base = 0;
	int i;
	for (i = 0; i < info->dlpi_phnum; i++) {
		if (info->dlpi_phdr[i].p_type == PT_LOAD &&
		    info->dlpi_phdr[i].p_flags & PF_X) {

			// Start and end of (relevant part of) section
			void *start = (void *)(info->dlpi_addr + info->dlpi_phdr[i].p_paddr);
			void *end = start + info->dlpi_phdr[i].p_filesz;

			// Find minimum, maximum
			if (!code_start || start < code_start)
				code_start = start;
			if (end > code_end)
				code_end = end;
			code_base = start - info->dlpi_phdr[i].p_offset;
		}
	}

	// No code found?
	if (code_start >= code_end)
		return 0;

	// Open file
	char *file = (char *)info->dlpi_name;
	if (!*file) {
		file = state->exe;
		state->exe = 0;
	}

	// Only first entry without name is this file. Others is boring
	// stuff like the stack.
	if (!file)
		return 0;

	dwarf_load_file(file, code_base, 0);
	return 0;
}

#endif // USE_DL_ITERATE_PHDR

void dwarf_load_file(char *module_path, seg_space *seg)
{

	// Open the module
	int fd = open(module_path, O_RDONLY);
	if (fd < 0) {
		sysErrorBelch("Could not open %s for reading debug data", module_path);
		return;
	}

	// Open using libelf (no archives, don't need elf_next)
	Elf *elf = elf_begin(fd, ELF_C_READ, 0);
	if(!elf) {
		errorBelch("Could not open ELF file: %s", elf_errmsg(elf_errno()));
		close(fd);
		return;
	}

	// Not actually an ELF file? That's okay, we are attempting this
	// for pretty much all memory-mapped files, so we can expect to
	// come across a few non-object files.
	if (elf_kind(elf) != ELF_K_ELF) {
		elf_end(elf);
		close(fd);
		return;
	}

	// Load debug data
	dwarf_load_ghc_debug_data(elf);

	// Find symbol address offset
	dwarf_get_code_bases(elf, seg);

	// Load symbols
	dwarf_load_symbols(module_path, elf, seg);

	// Open using libdwarf
	Dwarf_Debug dbg; Dwarf_Error err;
	if (dwarf_elf_init(elf, DW_DLC_READ, 0, 0, &dbg, &err) != DW_DLV_OK) {
		errorBelch("Could not read debug data from %s: %s", module_path, dwarf_errmsg(err));
		elf_end(elf);
		close(fd);
		return;
	}

	// Read compilation units
	nat cu;
	for (cu = 0; cu < 10000; cu++) {

		Dwarf_Unsigned cu_header_length = 0;
		Dwarf_Half version_stamp = 0;
		Dwarf_Off abbrev_offset = 0;
		Dwarf_Half address_size = 0;
		Dwarf_Unsigned next_cu_header = 0;
		Dwarf_Error error;

		// Get compilation unit header
		int res = dwarf_next_cu_header(dbg, &cu_header_length, &version_stamp,
									   &abbrev_offset, &address_size,
									   &next_cu_header, &error);
		if (res == DW_DLV_NO_ENTRY)
			break;
		if (res != DW_DLV_OK) {
			errorBelch("Could not read unit debug data from %s!", module_path);
			break;
		}

		// Get root die
		Dwarf_Die cu_die = 0;
		if (dwarf_siblingof(dbg, 0, &cu_die, &error) != DW_DLV_OK) {
			errorBelch("Could not a read root die from %s!", module_path);
			break;
		}

		// Check that it is, in fact, a compilation unit die
		Dwarf_Half tag = 0;
		if (dwarf_tag(cu_die, &tag, &error) != DW_DLV_OK
			|| tag != DW_TAG_compile_unit)
			continue;

		// Get name
		char *name = 0;
		if (dwarf_diename(cu_die, &name, &error) != DW_DLV_OK)
			continue;

		// Get compilation directory
		Dwarf_Attribute attr;
		char *comp_dir = 0;
		if (dwarf_attr(cu_die, DW_AT_comp_dir, &attr, &error) != DW_DLV_OK
			|| dwarf_formstring(attr, &comp_dir, &error) != DW_DLV_OK) {
			continue;
		}

		// Create unit, if necessary
		DwarfUnit *unit = dwarf_get_unit(name);
		if (!unit) unit = dwarf_new_unit(name, comp_dir);

		// Go through tree, log all ranges found
		dwarf_load_dies(unit, dbg, cu_die, seg);

	}

	// Done with DWARF
	Dwarf_Error error;
	dwarf_finish(dbg, &error);

	elf_end(elf);
	close(fd);
}

void dwarf_get_code_bases(Elf *elf, seg_space *segs)
{

	// Process all segments
	seg_space *seg;
	for (seg = segs; seg; seg = seg->next) {

		// Go through sections
		Elf_Scn *scn = 0;
		while ((scn = elf_nextscn(elf, scn))) {

			// Get section header
			GElf_Shdr hdr;
			if (!gelf_getshdr(scn, &hdr))
				continue;

			// Ignore non-executable sections
			if (!(hdr.sh_flags & SHF_EXECINSTR))
				continue;

			// This section not contained in the segment?
			size_t seg_len = (StgWord8 *)seg->end - (StgWord8 *)seg->start;
			if (hdr.sh_offset < seg->file_offset  ||
				hdr.sh_offset >= seg->file_offset + seg_len)
				continue;

			// Calculate the symbol offset.
			seg->base = (char *)seg->start - seg->file_offset - hdr.sh_addr + hdr.sh_offset;
			break;
		}
	}
}

void dwarf_load_ghc_debug_data(Elf *elf)
{

	// Get section header string table index
	size_t shdrstrndx;
	if (elf_getshdrstrndx(elf, &shdrstrndx))
		return;

	// Iterate over all sections
	Elf_Scn *scn = 0;
	while ((scn = elf_nextscn(elf, scn))) {

		// Get section header
		GElf_Shdr hdr;
		if (!gelf_getshdr(scn, &hdr))
			return;

		// Right name?
		char *name = elf_strptr(elf, shdrstrndx, hdr.sh_name);
		if (!name || strcmp(name, GHC_DEBUG_DATA_SECTION))
			continue;

		// Copy section contents to memory
		Elf_Data *data = 0;
		while ((data = elf_getdata(scn, data))) {
			if (!data->d_buf)
				continue;
			// Enlarge buffer, append data block
			dwarf_ghc_debug_data =
			    stgReallocBytes(dwarf_ghc_debug_data,
			                    dwarf_ghc_debug_data_size + data->d_size,
			                    "dwarf_load_ghc_debug_data");
			memcpy(((char *)dwarf_ghc_debug_data) + dwarf_ghc_debug_data_size,
			       data->d_buf,
			       data->d_size);
			dwarf_ghc_debug_data_size += data->d_size;
		}

		// Try to find more sections with matching name - this might
		// happen for example when compiling object files from LLVM
		// and the native back-end together: They set different section
		// flags, so they don't end up merged.
	}

}

// Use "FILE" type annotations in symbol table to find out which files
// the symbols originally came from. Sadly, this is not very useful
// until
//
// 1. The backend starts generating proper .file directives
//    into the assembler files. Probably straightforward for NCG,
//    sadly less easy for LLVM, where it would have to be hacked in
//    by the mangler, I think.
//
// 2. The linking stops discarding the generated FILE entries in
//    the symbol tables. Right now the -x flag to ld has them all
//    removed.
//
// On the other hand, being able to support this would make us
// independent from another dependency...

// #define GET_FILE_FROM_SYMTAB


// Catch-all unit to use where we don't have (or chose to ignore) a
// "file" entry in the symtab
#define SYMTAB_UNIT_NAME "SYMTAB: %s"

void dwarf_load_symbols(char *file, Elf *elf, seg_space *seg)
{

	// Locate symbol table section
	Elf_Scn *scn = 0; GElf_Shdr hdr;
	GElf_Shdr sym_shdr;
	GElf_Half sym_shndx = ~0;
	while ((scn = elf_nextscn(elf, scn))) {
		if (!gelf_getshdr(scn, &hdr))
			return;
		if (hdr.sh_type != SHT_SYMTAB && hdr.sh_type != SHT_DYNSYM)
			continue;
		// Get data
		Elf_Data *data = elf_getdata(scn, 0);
		if (!data)
			return;

		// Find or create the catch-all unit for symtab entries
		char symtab_unit_name[1024];
		snprintf (symtab_unit_name, 1024, SYMTAB_UNIT_NAME, file);
		DwarfUnit *unit = dwarf_get_unit(symtab_unit_name);
		if (!unit) unit = dwarf_new_unit(symtab_unit_name, "");

		// Iterate over symbols
		nat ndx;
		for (ndx = 1; ndx < hdr.sh_size / hdr.sh_entsize; ndx++) {

			// Get symbol data
			GElf_Sym sym;
			if (gelf_getsym(data, ndx, &sym) != &sym) {
				errorBelch("DWARF: Could not read symbol %d: %s\n", ndx, elf_errmsg(elf_errno()));
				continue;
			}

			// Look up string
			char *name = elf_strptr(elf, hdr.sh_link, sym.st_name);
			if (!name) {
				errorBelch("DWARF: Could not lookup name for symbol no %d: %s\n", ndx, elf_errmsg(elf_errno()));
				continue;
			}

			// Load associated section header. Use cached one where
			// applicable.
			if (sym.st_shndx != sym_shndx) {
				if (sym.st_shndx == SHN_ABS) {
					memset(&sym_shdr, 0, sizeof(sym_shdr));
				} else if(sym.st_shndx == SHN_UNDEF) {
					continue;
				} else {

					Elf_Scn *sym_scn = elf_getscn(elf, sym.st_shndx);
					if (gelf_getshdr(sym_scn, &sym_shdr) != &sym_shdr) {
						memset(&sym_shdr, 0, sizeof(sym_shdr));
					}
				}
				sym_shndx = sym.st_shndx;
			}

			// Type?
			switch (GELF_ST_TYPE(sym.st_info)) {

#ifdef GET_FILE_FROM_SYMTAB
			case STT_FILE:

				// Create unit, if necessary
				unit = dwarf_get_unit(name);
				if (!unit) unit = dwarf_new_unit(name, "");
				break;
#endif

			// Haskell symbols can appear in the symbol table flagged as
			// just about anything.
			case STT_NOTYPE:
			case STT_FUNC:
			case STT_OBJECT:

				// Only look at symbols from executable sections
				if (!(sym_shdr.sh_flags & SHF_EXECINSTR) ||
				    !(sym_shdr.sh_flags & SHF_ALLOC))
					continue;

				// Need a compilation unit to add name to. Ignore
				// unaccounted-for names.
				if (!unit)
					break;

				// Add procedure
				dwarf_new_proc(unit, name,
				               sym.st_value, sym.st_value+sym.st_size,
				               DwarfSourceSymtab, seg);

				break;
			}
		}

	}
}


void dwarf_load_dies(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, seg_space *seg)
{

	// Load data from node
	dwarf_load_proc_die(unit, dbg, die, seg);
	dwarf_load_block_die(unit, dbg, die, seg);

	// Recurse
	Dwarf_Error error; Dwarf_Die child;
	int res;
	for (res = dwarf_child(die, &child, &error);
	     res == DW_DLV_OK;
	     res = dwarf_siblingof(dbg, child, &child, &error)) {

		dwarf_load_dies(unit, dbg, child, seg);

	}

}

static char *dwarf_findname(Dwarf_Die die) {

	// Try MIPS_linkage_name first
	char *name;
	Dwarf_Attribute attr;
	Dwarf_Error error;
	if (dwarf_attr(die, DW_AT_MIPS_linkage_name, &attr, &error) == DW_DLV_OK
	    && dwarf_formstring(attr, &name, &error) == DW_DLV_OK)
		return name;

	// Then the "normal" name
	if (dwarf_diename(die, &name, &error) == DW_DLV_OK)
		return name;

	return 0;
}

void dwarf_load_proc_die(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, seg_space *seg)
{

	// Get node tag
	Dwarf_Half tag = 0;
	Dwarf_Error error;
	if (dwarf_tag(die, &tag, &error) != DW_DLV_OK)
		return;

	// Only interested in procedures (inlined or not)
	char *name = 0;
	if (tag != DW_TAG_subprogram && tag != DW_TAG_inlined_subroutine)
		return;

	// Try to get name directly
	Dwarf_Attribute attr;
	if ( !(name = dwarf_findname(die)) ) {

		// Locate abstract origin node, get name from there
		Dwarf_Off ref; Dwarf_Die proc_die;
		if (dwarf_attr(die, DW_AT_abstract_origin, &attr, &error) != DW_DLV_OK
		    || dwarf_global_formref(attr, &ref, &error) != DW_DLV_OK
		    || dwarf_offdie(dbg, ref, &proc_die, &error) != DW_DLV_OK
		    || !(name = dwarf_findname(proc_die))) {

			ref = 0;
			dwarf_dieoffset(die, &ref, &error);
			errorBelch("DWARF <%x>: subroutine without name or abstract origin!\n", (unsigned int)ref);
			return;
		}
	}

	// Get IP range
	Dwarf_Addr low_pc, high_pc;
	if (dwarf_attr(die, DW_AT_low_pc, &attr, &error) != DW_DLV_OK
	    || dwarf_formaddr(attr, &low_pc, &error) != DW_DLV_OK
	    || dwarf_attr(die, DW_AT_high_pc, &attr, &error) != DW_DLV_OK
	    || dwarf_formaddr(attr, &high_pc, &error) != DW_DLV_OK) {

		// This might happen for subroutines which only appear
		// inlined. Those will have a DW_TAG_inlined_subroutine entry
		// somewhere pointing here, so we can safely ignore the node
		// for now.
		return;
	}

	// Create the new procedure entry
	dwarf_new_proc(unit, name, low_pc, high_pc, DwarfSourceDwarf, seg);

}

void dwarf_load_block_die(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, seg_space *seg)
{

    // Only interested in lexical blocks here
    Dwarf_Half tag = 0;
    Dwarf_Error error;
    if (dwarf_tag(die, &tag, &error) != DW_DLV_OK
        || tag != DW_TAG_lexical_block)
        return;

    // Block has a name?
    char *bname = 0;
    if (dwarf_diename(die, &bname, &error) != DW_DLV_OK) {

        // Fallback to looking for a variable starting with
        // "__debug_ghc_" (marker inserted by LLVM backend, as we
        // can't name blocks there).
        char *MARKER_PREFIX = "__debug_ghc_";
        int marker_len = strlen(MARKER_PREFIX);
        Dwarf_Die bchild;
        Dwarf_Half btag = 0;
        int res;
        for (res = dwarf_child(die, &bchild, &error);
             res == DW_DLV_OK;
             res = dwarf_siblingof(dbg, bchild, &bchild, &error)) {

            if (dwarf_tag(bchild, &btag, &error) != DW_DLV_OK
                || btag != DW_TAG_variable)
                continue;

            // Get name, check prefix
            if (dwarf_diename(bchild, &bname, &error) != DW_DLV_OK
                || strncmp(bname, MARKER_PREFIX, marker_len)) {
                bname = 0;
                continue;
            }

            // Go over prefix - the rest of the string is the name of
            // the block this code was generated from.
            bname += marker_len;
            break;
        }

    }

    // Marker not found? Then this lexical block isn't interesting to
    // us.
    if (!bname)
        return;

    // Check if there is a simple low-pc/high-pc pair annotation
	Dwarf_Attribute attr;
    Dwarf_Addr low_pc, high_pc;
    if (dwarf_attr(die, DW_AT_low_pc, &attr, &error) != DW_DLV_OK
        || dwarf_formaddr(attr, &low_pc, &error) != DW_DLV_OK
        || dwarf_attr(die, DW_AT_high_pc, &attr, &error) != DW_DLV_OK
        || dwarf_formaddr(attr, &high_pc, &error) != DW_DLV_OK) {

        // ... or possibly a more cumbersome range list
        Dwarf_Off range_off;
        if (dwarf_attr(die, DW_AT_ranges, &attr, &error) != DW_DLV_OK
            || dwarf_global_formref(attr, &range_off, &error) != DW_DLV_OK) {

            // No info? stop
            return;

        }

        // Get range list
        Dwarf_Ranges *ranges = 0;
        Dwarf_Signed cnt = 0;
        Dwarf_Unsigned bytes = 0;
        if (dwarf_get_ranges_a(dbg,range_off,die,
                               &ranges,&cnt,&bytes,&error) != DW_DLV_OK)
            return;

        // Emit a procedure for each range. Note this is pretty
        // inefficient - but we don't expect this to happen too often,
        // so it should be okay.
        Dwarf_Signed i;
        for (i = 0; i < cnt; i++) {
            dwarf_new_proc(unit, bname, ranges[i].dwr_addr1, ranges[i].dwr_addr2,
                           DwarfSourceDwarfBlock, seg);
        }

        // Dealloc range list
        dwarf_ranges_dealloc(dbg, ranges, cnt);

    } else {

        // So we have a block with simple high_pc/low_pc
        // annotation. Emit an entry for it.
        dwarf_new_proc(unit, bname, low_pc, high_pc, DwarfSourceDwarfBlock, seg);


    }

}

DwarfUnit *dwarf_get_unit(char *name)
{
	DwarfUnit *unit;
	for (unit = dwarf_units; unit; unit = unit->next)
		if (!strcmp(name, unit->name))
			return unit;
	return 0;
}

DwarfUnit *dwarf_new_unit(char *name, char *comp_dir)
{
	DwarfUnit *unit = (DwarfUnit *)stgMallocBytes(sizeof(DwarfUnit), "dwarf_new_unit");
	unit->name = strdup(name);
	unit->comp_dir = strdup(comp_dir);
	unit->low_pc = NULL;
	unit->high_pc = NULL;
	unit->debug_data = NULL;
	unit->procs = NULL;
	unit->proc_count = 0;
	unit->max_proc_id = 0;
	unit->proc_table = allocStrHashTable();
	unit->procs_by_id = NULL;
	unit->procs_by_pc = NULL;
	unit->next = dwarf_units;
	dwarf_units = unit;
	return unit;
}

DwarfProc *dwarf_get_proc(DwarfUnit *unit, char *name)
{
	return lookupStrHashTable(unit->proc_table, name);
}

DwarfProc *dwarf_new_proc(DwarfUnit *unit, char *name,
                          Dwarf_Addr low_pc, Dwarf_Addr high_pc,
                          DwarfSource source,
                          seg_space *segs)
{
	// Security
	if (high_pc <= low_pc)
		return NULL;

	// Apply offset to translate into our address space, then
	// range-check so we don't associate it with the wrong
	// memory region.
	void *low_pc_ptr = NULL, *high_pc_ptr = NULL;
	seg_space *seg;
	for (seg = segs; seg; seg = seg->next) {
		low_pc_ptr = (char *)seg->base + low_pc;
		high_pc_ptr = (char *)seg->base + high_pc;

		if ((char *)low_pc_ptr < (char *)seg->start ||
			(char *)high_pc_ptr > (char *)seg->end) {

			low_pc_ptr = high_pc_ptr = NULL;
		}
	}
	if (!low_pc_ptr)
		return NULL;

	// Already have the proc? This can happen when there are multiple
	// inlinings.
	DwarfProc *after = dwarf_get_proc(unit, name);

    // Always create new procedure entry no matter whether we already
    // have the procedure or not (could optimize this in future...)
	DwarfProc *proc = (DwarfProc *)stgMallocBytes(sizeof(DwarfProc), "dwarf_new_proc");
	proc->name = strdup(name);
	proc->id = proc->parent_id = GHC_DEBUG_NO_ID;
	proc->low_pc = low_pc_ptr;
	proc->high_pc = high_pc_ptr;
	proc->source = source;
	proc->debug_data = NULL;

	proc->next = (after ? after->next : unit->procs);
	*(after ? &after->next : &unit->procs) = proc;

	// Update unit data
	if (!after)
		insertStrHashTable(unit->proc_table, proc->name, proc);
	if (!unit->low_pc || low_pc_ptr < unit->low_pc)
		unit->low_pc = low_pc_ptr;
	if (!unit->high_pc || high_pc_ptr > unit->high_pc)
		unit->high_pc = high_pc_ptr;
	unit->proc_count++;

	return proc;
}

void dwarf_free()
{
	DwarfUnit *unit;
	while ((unit = dwarf_units)) {
		dwarf_units = unit->next;
		freeHashTable(unit->proc_table, NULL);
		free(unit->procs_by_id);
		free(unit->procs_by_pc);

		DwarfProc *proc;
		while ((proc = unit->procs)) {
			unit->procs = proc->next;
			free(proc->name);
			free(proc);
		}

		free(unit->name);
		free(unit->comp_dir);
		free(unit);
	}
	free(dwarf_ghc_debug_data);
	dwarf_ghc_debug_data = 0;
}

// Read a little-endian StgWord16
StgWord16 word16LE(StgWord8 *p) {
	StgWord8 high = *p++;
	StgWord8 low = *p;
	return (((StgWord16) high) << 8) + low;
}

// Builds up associations between debug and DWARF data. If "trace"
// parameter is set, we also trace all information (presumably
// to copy it into an eventlog).

void dwarf_associate_debug_data(StgBool trace)
{
	(void)(trace); // unused

	// Go through available debugging data
	StgWord8 *dbg = (StgWord8 *)dwarf_ghc_debug_data;
	StgWord8 *dbg_limit = dbg + dwarf_ghc_debug_data_size;
	DwarfUnit *unit = 0;
	while (dbg && dbg < dbg_limit) {

		// Ignore zeroes
		if (!*dbg) {
			dbg++;
			continue;
		}
		StgWord8 *debug_data = dbg;

		// Get event type and size. Note that utils/Binary.hs writes
		// StdWord16 as little-endian.
		EventTypeNum num = (EventTypeNum) *dbg; dbg++;
		StgWord16 size = word16LE(dbg); dbg += 2;

		// Sanity-check size
		if (dbg + size > dbg_limit) {
			errorBelch("Debug data packet num %d exceeds section size! Probably corrupt debug data.", num);
			break;
		}

		// Follow data
		char *proc_name = 0, *unit_name = 0;
		StgWord16 proc_id = GHC_DEBUG_NO_ID, proc_parent_id = GHC_DEBUG_NO_ID;
		DwarfProc *proc = 0;
		switch (num) {

		case EVENT_DEBUG_MODULE: // package, name, ...

			// Get unit (with minimal added security)
			if (strlen((char *)dbg) >= size) break;
			unit_name = ((char *)dbg) + strlen((char *)dbg) + 1;
			if (strlen((char *)dbg) + strlen(unit_name) + 1 >= size) {
				errorBelch("Missing string terminator for module record! Probably corrupt debug data.");
				return;
			}
			unit = dwarf_get_unit(unit_name);
			if (unit) unit->debug_data = debug_data;
			break;

		case EVENT_DEBUG_BLOCK: // instr, parent, name, ...
			if (!unit) break;
			proc_id = word16LE(dbg);
			if (proc_id > unit->max_proc_id)
				unit->max_proc_id = proc_id;
			proc_parent_id = word16LE(dbg + 2);
			proc_name = (char *)dbg + 4;
			proc = dwarf_get_proc(unit, proc_name);
			break;

		default: break;
		}

		// Post data
		dbg += size;

		// Post debug data of procedure. Note we might have
		// multiple entries and therefore IP ranges!
		if (!proc) continue;
		do {
			proc->id = proc_id;
			proc->parent_id = proc_parent_id;
			proc->debug_data = debug_data;
			proc = proc->next;
		}
        while (proc && !strcmp(proc_name, proc->name));
	}

}

int compare_low_pc(const void *a, const void *b);
int compare_low_pc(const void *a, const void *b) {
	DwarfProc *proca = *(DwarfProc **)a;
	DwarfProc *procb = *(DwarfProc **)b;
	if (proca->low_pc < procb->low_pc) return -1;
	if (proca->low_pc == procb->low_pc) {
		if (procb->source == DwarfSourceDwarfBlock)
			return -1;
		else if(proca->source == DwarfSourceDwarfBlock)
			return 1;
		else
			return 0;
	}
	return 1;
}

void dwarf_dump_tables(DwarfUnit *unit);
void dwarf_dump_tables(DwarfUnit *unit)
{
	StgWord i;
	printf(" Unit %s (%lu procs, %d max id) %p-%p:\n",
	       unit->name, unit->proc_count, unit->max_proc_id,
	       unit->low_pc, unit->high_pc);
	for (i = 0; i < unit->proc_count; i++) {
		printf("%p-%p: %s\n",
			   unit->procs_by_pc[i]->low_pc, unit->procs_by_pc[i]->high_pc,
			       unit->procs_by_pc[i]->name);
	}
	for (i = 0; i <= unit->max_proc_id; i++)
		if (unit->procs_by_id[i]) {
			printf("%5lu: %s (p %d)\n", i,
			       unit->procs_by_id[i]->name, unit->procs_by_id[i]->parent_id);
		} else {
			printf("%5lu: (null)\n", i);
		}
}

void dwarf_init_lookup(void)
{
	// Read debug data - will be used later in actual lookups. For the
	// moment, we primarily want the procedure IDs so we can build the
	// table.
	dwarf_associate_debug_data(0);

	// Build procedure tables for every unit
	DwarfUnit *unit;
	for (unit = dwarf_units; unit; unit = unit->next) {

		// Just in case we run this twice for some reason
		free(unit->procs_by_id); unit->procs_by_id = NULL;
		free(unit->procs_by_pc); unit->procs_by_pc = NULL;

		// Allocate tables
		StgWord pcTableSize = unit->proc_count * sizeof(DwarfProc *);
		StgWord idTableSize = (unit->max_proc_id + 1) * sizeof(DwarfProc *);
		unit->procs_by_pc = (DwarfProc **)stgMallocBytes(pcTableSize, "dwarf_init_pc_table");
		unit->procs_by_id = (DwarfProc **)stgMallocBytes(idTableSize, "dwarf_init_id_table");
		memset(unit->procs_by_id, 0, idTableSize);

		// Populate
		StgWord i = 0;
		DwarfProc *proc;
		for (proc = unit->procs; proc; proc = proc->next) {
			unit->procs_by_pc[i++] = proc;
			if (proc->id != GHC_DEBUG_NO_ID && proc->id <= unit->max_proc_id)
				unit->procs_by_id[proc->id] = proc;
		}

		// Sort PC table by low_pc
		qsort(unit->procs_by_pc, unit->proc_count, sizeof(DwarfProc *), compare_low_pc);

	}
}

DwarfProc *dwarf_lookup_proc(void *ip, DwarfUnit **punit)
{
	DwarfUnit *unit;
	for (unit = dwarf_units; unit; unit = unit->next) {

		// Pointer in unit range?
		if (ip < unit->low_pc || ip >= unit->high_pc)
			continue;
		if (!unit->proc_count || !unit->procs_by_pc)
			continue;

		// Find first entry with low_pc < ip in table (using binary search)
		StgWord low = 0, high = unit->proc_count;
		while (low < high) {
			int mid = (low + high) / 2;
			if (unit->procs_by_pc[mid]->low_pc <= ip)
				low = mid + 1;
			else
				high = mid;
		}

		// Find an entry covering it
		while (low > 0) {
			DwarfProc *proc = unit->procs_by_pc[low-1];

			// Security
			if (ip < proc->low_pc) {
				debugBelch("DWARF lookup: PC table corruption!");
				break;
			}

			// In bounds? Then we have found it
			if (ip <= proc->high_pc) {
				if (punit)
					*punit = unit;
				return proc;
			}

			// Not a block? Stop search
			if (proc->source != DwarfSourceDwarfBlock)
				break;

			// Otherwise backtrack
			low--;
		}

	}

	return NULL;
}

StgWord dwarf_get_debug_info(DwarfUnit *unit, DwarfProc *proc, DebugInfo *infos, StgWord max_infos)
{
	// Read debug information
	StgWord8 *dbg = proc->debug_data;
	StgWord8 *dbg_limit = (StgWord8 *)dwarf_ghc_debug_data + dwarf_ghc_debug_data_size;
	StgBool gotProc = 0;
	StgBool stopRecurse = 0;
	StgWord info = 0;
	StgWord depth = 0;
	while (dbg && dbg <= dbg_limit && info < max_infos) {

		// Get ID and size
		EventTypeNum num = (EventTypeNum) *dbg; dbg++;
		StgWord16 size = word16LE(dbg); dbg += 2;

		// Check record type
		StgBool done = 0;
		switch (num) {
		case EVENT_DEBUG_BLOCK:
			// First time is expected, next means we have reached the
			// end of records belonging to this proc
			if (!gotProc)
				gotProc = 1;
			else
				done = 1;
			break;

		// This is what we are looking for: Data to copy
		case EVENT_DEBUG_SOURCE: {
			infos[info].sline = word16LE(dbg);
			infos[info].scol  = word16LE(dbg+2);
			infos[info].eline = word16LE(dbg+4);
			infos[info].ecol  = word16LE(dbg+6);
			int len = strlen((char *)dbg+8),
			    len2 = strlen((char *)dbg+9+len);
			if (10 + len + len2 > size) {
				errorBelch("Missing string terminator for module record! Probably corrupt debug data.");
				return info;
			}
			infos[info].file = (char *)dbg+8;
			infos[info].name = (char *)dbg+9+len;
			infos[info].depth = depth;
			info++;
			// Did we find a source annotation for our own module?
			if (!strcmp(infos[info-1].file, unit->name)) {
				// Stop recursing to parents then - that would only
				// dull the precision.
				stopRecurse = 1;
				return info;
			}
			break;
		}

		// These can be safely ignored
		case EVENT_DEBUG_CORE:
		   break;

		// Unknown events must be considered stoppers.
		default:
		   done = 1;
		}
		dbg += size;

		// Finished with this proc?
		if (done) {
			// Try to jump to parent
			if (!stopRecurse &&
			    proc->parent_id <= unit->max_proc_id &&
			    (proc = unit->procs_by_id[proc->parent_id])) {

				// Continue at parent
				dbg = proc->debug_data;
				gotProc = 0;
				depth++;
			} else {
				break;
			}
		}
	}
	return info;
}

#endif /* USE_DWARF */
