
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

static void *dwarf_get_code_offset(Elf *elf, void *seg_start);
static void dwarf_load_ghc_debug_data(Elf *elf);
static void dwarf_load_symbols(char *file, Elf *elf, void *seg_start);

static void dwarf_load_file(char *module_path, void *seg_start);
static void dwarf_load_dies(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, void *seg_start);
static void dwarf_load_die(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, void *seg_start);

static DwarfUnit *dwarf_new_unit(char *name, char *comp_dir);
static DwarfProc *dwarf_new_proc(DwarfUnit *unit, char *name, void *low_pc, void *high_pc,
                                 DwarfSource source, DwarfProc *after);

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
		barf("libelf version too old!");
		return;
	}

	// Open our process' memory map
	FILE *map_file = fopen("/proc/self/maps", "r");
	if (!map_file) {
		sysErrorBelch("Could not read /proc/self/map!");
		return;
	}

	// Read out mappings
	char line[1025];
	while (!feof(map_file)) {

		// Read a line
		void *seg_start = 0;
		char exec_perm = '-';
		char module_path[255+1] = "";
		unsigned int offset;
		if (!fgets(line, 1024, map_file))
			break;
		if (!sscanf(line, "%p-%*p %*c%*c%c%*c %x %*x:%*x %*d %255s",
		            &seg_start, &exec_perm, &offset, module_path) > 0)
			break;

		// Load if it is an executable section
		if (exec_perm == 'x' && module_path[0] != '[')
			dwarf_load_file(module_path, (char *)seg_start - offset);

	}

	fclose(map_file);
}

#else // USE_DL_ITERATE_PHDR

int dwarf_load_by_phdr(struct dl_phdr_info *info, size_t size, void *data);

void dwarf_load()
{
	// Initialize ELF library
	if (elf_version(EV_CURRENT) == EV_NONE) {
		barf("libelf version too old!");
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

			// Gross hack. For some reason

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

void dwarf_load_file(char *module_path, void *seg_start)
{

	// Open the module
	int fd = open(module_path, O_RDONLY);
	if (fd < 0) {
		sysErrorBelch("Could not open %s for reading debug data!", module_path);
		return;
	}

	// Open using libelf (no archives, don't need elf_next)
	Elf *elf = elf_begin(fd, ELF_C_READ, 0);
	if(!elf) {
		barf("Could not open ELF file: %s", elf_errmsg(elf_errno()));
		return;
	}

	// Load debug data
	dwarf_load_ghc_debug_data(elf);

	// Load symbols
	dwarf_load_symbols(module_path, elf, seg_start);

	// Find symbol address offset
	void *code_offset = dwarf_get_code_offset(elf, seg_start);

	// Open using libdwarf
	Dwarf_Debug dbg; Dwarf_Error err;
	if (dwarf_elf_init(elf, DW_DLC_READ, 0, 0, &dbg, &err) != DW_DLV_OK) {
		sysErrorBelch("Could not read debug data from %s!", module_path);
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
			return;
		}

		// Get root die
		Dwarf_Die cu_die = 0;
		if (dwarf_siblingof(dbg, 0, &cu_die, &error) != DW_DLV_OK) {
			errorBelch("Could not a read root die from %s!", module_path);
			return;
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
		dwarf_load_dies(unit, dbg, cu_die, code_offset);

	}

	// Done with DWARF
	Dwarf_Error error;
	dwarf_finish(dbg, &error);

	elf_end(elf);
	close(fd);
}

void *dwarf_get_code_offset(Elf *elf, void *seg_start)
{

	// Go through sections
	Elf_Scn *scn = 0;
	while ((scn = elf_nextscn(elf, scn))) {

		// Get section header
		GElf_Shdr hdr;
		if (!gelf_getshdr(scn, &hdr))
			continue;

		// Executable section?
		if (!(hdr.sh_flags & SHF_EXECINSTR) ||
		    !(hdr.sh_flags & SHF_ALLOC))
			continue;

		// Calculate the symbol offset.
		//
		// Note that just returning the right offset for the first
		// text section we come across is actually dangerous, as there
		// could be others with different offsets. Yet this doesn't
		// seem to happen in practice, so we save us the effort to
		// build a real memory map here.
		return (char *)seg_start - hdr.sh_addr + hdr.sh_offset;
	}

	// Just assume a zero offset otherwise
	return 0;
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

void dwarf_load_symbols(char *file, Elf *elf, void *seg_start)
{

	// Locate symbol table section
	Elf_Scn *scn = 0; GElf_Shdr hdr;
	GElf_Shdr sym_shdr;
	GElf_Half sym_shndx = ~0;
	void *sym_offset = 0;
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
				barf("DWARF: Could not read symbol %d: %s\n", ndx, elf_errmsg(elf_errno()));
				continue;
			}

			// Look up string
			char *name = elf_strptr(elf, hdr.sh_link, sym.st_name);
			if (!name) {
				barf("DWARF: Could not lookup name for symbol no %d: %s\n", ndx, elf_errmsg(elf_errno()));
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
						sym_offset = (char *)seg_start - sym_shdr.sh_addr + sym_shdr.sh_offset;
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

				// Add procedure
				dwarf_new_proc(unit, name,
				               (char *)sym_offset+sym.st_value,
				               (char *)sym_offset+sym.st_value+sym.st_size,
				               DwarfSourceSymtab, 0);
				break;
			}
		}

	}
}


void dwarf_load_dies(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, void *code_offset)
{

	// Load data from node
	dwarf_load_die(unit, dbg, die, code_offset);

	// Recurse
	Dwarf_Error error; Dwarf_Die child;
	int res;
	for (res = dwarf_child(die, &child, &error);
	     res == DW_DLV_OK;
	     res = dwarf_siblingof(dbg, child, &child, &error)) {

		dwarf_load_dies(unit, dbg, child, code_offset);

	}

}

void dwarf_load_die(DwarfUnit *unit, Dwarf_Debug dbg, Dwarf_Die die, void *code_offset)
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
	if (dwarf_diename(die, &name, &error) != DW_DLV_OK) {

		// Locate abstract origin node, get name from there
		Dwarf_Attribute attr; Dwarf_Off ref; Dwarf_Die proc_die;
		if (dwarf_attr(die, DW_AT_abstract_origin, &attr, &error) != DW_DLV_OK
		    || dwarf_global_formref(attr, &ref, &error) != DW_DLV_OK
		    || dwarf_offdie(dbg, ref, &proc_die, &error) != DW_DLV_OK
		    || dwarf_diename(proc_die, &name, &error) != DW_DLV_OK) {

			ref = 0;
			dwarf_dieoffset(die, &ref, &error);
			barf("DWARF <%x>: subroutine without name or abstract origin!\n", ref);
			return;
		}
	}

	// Get IP range
	Dwarf_Addr low_pc, high_pc;
	Dwarf_Attribute attr;
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

	// Apply offset to translate into our address space
	// TODO: Check this is actually doing the right thing, haven't
	//       tested with dynamic libs so far
	void *low_pc_ptr = (char *)code_offset + low_pc;
	void *high_pc_ptr = (char *)code_offset + high_pc;

	// Already have the proc? This can happen when there are multiple
	// inlinings.
	DwarfProc *proc = dwarf_get_proc(unit, name);

	// We insert a new entry anyway - directly after the existing one,
	// if applicable.
	dwarf_new_proc(unit, name, low_pc_ptr, high_pc_ptr, DwarfSourceDwarf, proc);

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
                          void *low_pc, void *high_pc,
                          DwarfSource source,
                          DwarfProc *after)
{

	DwarfProc *proc = (DwarfProc *)stgMallocBytes(sizeof(DwarfProc), "dwarf_new_proc");
	proc->name = strdup(name);
	proc->low_pc = low_pc;
	proc->high_pc = high_pc;
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
	DwarfUnit *unit = 0;
	while (dbg && dbg < (StgWord8 *)dwarf_ghc_debug_data + dwarf_ghc_debug_data_size) {

		// Ignore zeroes
		if (!*dbg) {
			dbg++;
			continue;
		}

		// Get event type and size.
		EventTypeNum num = (EventTypeNum) *dbg; dbg++;
		StgWord16 size = *(StgWord16 *)dbg; dbg += sizeof(StgWord16);

		// Follow data
		char *proc_name = 0;
		DwarfProc *proc = 0;
		switch (num) {

		case EVENT_DEBUG_MODULE: // name, ...

			// If we had a unit before: Trace all data we didn't see a
			// matching proc for
			if (unit) dwarf_trace_unaccounted(unit, 0);

			// Get unit (with minimal added security)
			if (strlen((char *)dbg) >= size) break;
			unit = dwarf_get_unit((char *)dbg);
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
				traceModule(unit->name, 0, 0);
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
