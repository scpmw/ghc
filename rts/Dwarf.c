
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

#ifdef TRACING
static void dwarf_trace_all_unaccounted(void);
static void dwarf_trace_unaccounted(DwarfUnit *unit, StgBool put_module);
#endif // TRACING

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
			seg_space *seg = (seg_space *)stgMallocBytes(sizeof(DwarfUnit), "dwarf_new_unit");
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

	// Load symbols
	dwarf_load_symbols(module_path, elf, seg);

	// Find symbol address offset
	dwarf_get_code_bases(elf, seg);

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

		return;
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
	Dwarf_Addr sym_offset = 0;
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
					sym_offset = 0;
					memset(&sym_shdr, 0, sizeof(sym_shdr));
				} else if(sym.st_shndx == SHN_UNDEF) {
					continue;
				} else {

					Elf_Scn *sym_scn = elf_getscn(elf, sym.st_shndx);
					if (gelf_getshdr(sym_scn, &sym_shdr) == &sym_shdr) {
						sym_offset = sym_shdr.sh_offset - sym_shdr.sh_addr;
					} else {
						sym_offset = 0;
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

				{
					Dwarf_Addr start = sym_offset+sym.st_value;
					Dwarf_Addr end = start+sym.st_size;

					// Add procedure
					dwarf_new_proc(unit, name,
					               start, end,
					               DwarfSourceSymtab, seg);

				}
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
			errorBelch("DWARF <%x>: subroutine without name or abstract origin!\n", ref);
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

    // Find a variable starting with "__debug_ghc_" - this is our marker.
    char *MARKER_PREFIX = "__debug_ghc_";
    int marker_len = strlen(MARKER_PREFIX);
    Dwarf_Die bchild;
    Dwarf_Half btag = 0;
    char *bname = 0;
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
	unit->procs = 0;
	unit->next = dwarf_units;
	unit->proc_table = allocStrHashTable();
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
	// TODO: Check this is actually doing the right thing, haven't
	//		 tested with dynamic libs so far
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
	proc->low_pc = low_pc_ptr;
	proc->high_pc = high_pc_ptr;
	proc->source = source;
	proc->copied = 0;

	proc->next = (after ? after->next : unit->procs);
	*(after ? &after->next : &unit->procs) = proc;

	if (!after)
		insertStrHashTable(unit->proc_table, proc->name, proc);

	return proc;
}

void dwarf_free()
{
	DwarfUnit *unit;
	while ((unit = dwarf_units)) {
		dwarf_units = unit->next;
		freeHashTable(unit->proc_table, NULL);

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

#ifdef TRACING

// Writes debug data to the event log, enriching it with DWARF
// debugging information where possible

void dwarf_trace_debug_data()
{
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

		// Get event type and size. Note that utils/Binary.hs writes
		// StdWord16 as little-endian.
		EventTypeNum num = (EventTypeNum) *dbg; dbg++;
		StgWord8 sizeh = *dbg++; StgWord8 sizel = *dbg++;
		StgWord16 size = (((StgWord16)sizeh) << 8) + sizel;

		// Sanity-check size
		if (dbg + size >= dbg_limit) {
			errorBelch("Debug data packet num %d exceeds section size! Probably corrupt debug data.", num);
			break;
		}

		// Follow data
		char *proc_name = 0, *unit_name = 0;
		DwarfProc *proc = 0;
		switch (num) {

		case EVENT_DEBUG_MODULE: // package, name, ...

			// If we had a unit before: Trace all data we didn't see a
			// matching proc for
			if (unit) dwarf_trace_unaccounted(unit, 0);

			// Get unit (with minimal added security)
			if (strlen((char *)dbg) >= size) break;
			unit_name = ((char *)dbg) + strlen((char *)dbg) + 1;
			if (strlen((char *)dbg) + strlen(unit_name) + 1 >= size) break;
			unit = dwarf_get_unit(unit_name);
			break;

		case EVENT_DEBUG_PROCEDURE: // instr, parent, name, ...
			if (!unit) break;
			proc_name = (char *)dbg + sizeof(StgWord16) + sizeof(StgWord16);
			proc = dwarf_get_proc(unit, proc_name);
			break;

		default: break;
		}

		// Post data
		traceDebugData(num, size, dbg);
		dbg += size;

		// Post additional data about procedure. Note we might have
		// multiple ranges per procedure!
		while (proc && !strcmp(proc_name, proc->name)) {
			traceProcPtrRange(proc->low_pc, proc->high_pc);
			proc->copied = 1;
			proc = proc->next;
		}
	}

	// Add all left-over debug info
	if (unit)
		dwarf_trace_unaccounted(unit, 0);
	dwarf_trace_all_unaccounted();
}

// Writes out information about all procedures that we don't have
// entries in the debugging info for - but still know something
// interesting about, like their procedure name is and where the code
// was coming from. This will, for example, catch libraries without
// debug info as well as RTS stuff.

void dwarf_trace_all_unaccounted()
{
	DwarfUnit *unit;

	for (unit = dwarf_units; unit; unit = unit->next) {
		dwarf_trace_unaccounted(unit, 1);
	}
}

void dwarf_trace_unaccounted(DwarfUnit *unit, StgBool put_module)
{
	DwarfProc *proc;

	for (proc = unit->procs; proc; proc = proc->next)
		if (!proc->copied) {

			// Need to put module header?
			if (put_module) {
				traceDebugModule(unit->name);
				put_module = 0;
			}

			// Print everything we know about the procedure
			traceDebugProc(proc->name);
			traceProcPtrRange(proc->low_pc, proc->high_pc);
			proc->copied = 1;

		}
}

#endif /* TRACING */

#endif /* USE_DWARF */
