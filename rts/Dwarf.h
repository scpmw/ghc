
#ifndef DWARF_H
#define DWARF_H

#include "BeginPrivate.h"

#ifdef USE_DWARF

typedef struct DwarfUnit_ DwarfUnit;
typedef struct DwarfProc_ DwarfProc;
typedef enum DwarfSource_ DwarfSource;

struct DwarfUnit_ {
	char *name;
	char *comp_dir;
	DwarfProc *procs;
	DwarfUnit *next;
};

enum DwarfSource_ {
	DwarfSourceDwarf,
	DwarfSourceSymtab,
};

struct DwarfProc_ {
	char *name;
	void *low_pc;
	void *high_pc;
	StgBool copied;
	DwarfSource source;
	struct DwarfProc_ *next;
};

extern DwarfUnit *dwarf_units;

void dwarf_load(void);
DwarfUnit *dwarf_get_unit(char *name);
DwarfProc *dwarf_get_proc(DwarfUnit *unit, char *name);
void dwarf_free(void);

#endif // USE_DWARF

#include "EndPrivate.h"

#endif // DWARF_H
