
#include "Rts.h"

#include "Dwarf.h"

#include "libdwarf/dwarf.h"
#include "libdwarf/libdwarf.h"

#include <sys/types.h>
#include <unistd.h>
#include <stdio.h>

void dwarf_dump_module(const char *module_path, void *seg_start, StgWord offset);

void dwarf_dump_all() {
	FILE *map_file;

	// Open our process' memory map
	map_file = fopen("/proc/self/map", "r");
	if (!map_file) {
		sysErrorBelch("Could not read /proc/self/map!");
		return;
	}

	// Read out mappings
	for(;;) {

		// Read a line
		void *seg_start = 0;
		char exec_perm = '-';
		char module_path[255+1] = "";
		StgWord offset;
		if (!fscanf(map_file, "%p-%*p %*c%*c%c%*c %x %*x:%*x %*d %255s",
		            &seg_start, &exec_perm, &offset, &module_path) > 0)
			break;
		
		// Go to next newline
		char c;
		while (c = fgetc(map_file))
			if (c == '\n')
				break;

		// Dump if it is an executable section
		if (exec_perm == 'x')
			dwarf_dump_module(module_path, seg_start);

	}

	fclose(map_file);
}

void dwarf_dump_module(const char *module_path, void *seg_start, StgWord offset) {

	// Open the module
	int fd = open(module_path, O_RDONLY);
	if (fd < 0) {
		sysErrorBelch("Could not open %s for reading debug data!");
		return;
	}

	Dwarf_Debug dbg; Dwarf_Error err;
	if (dwarf_init(fd, DW_DLC_READ, 0, 0, &dbg, &err) != DW_DLV_OK) {
		sysErrorBelch("Could not read debug data from %s!");
		close(fd);
		return;
	}

	
}
