
#ifndef DWARF_H
#define DWARF_H

#include "BeginPrivate.h"

#ifdef USE_DWARF

#include "Hash.h"

typedef struct DwarfUnit_ DwarfUnit;
typedef struct DwarfProc_ DwarfProc;
typedef enum DwarfSource_ DwarfSource;

struct DwarfUnit_ {
	char *name;
	char *comp_dir;
	DwarfProc *procs;
	DwarfUnit *next;
	HashTable *proc_table;
};

enum DwarfSource_ {
	DwarfSourceDwarf,
	DwarfSourceDwarfBlock,
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

#ifdef TRACING
void dwarf_trace_debug_data(void);
#endif // TRACING

#endif // USE_DWARF

#include "EndPrivate.h"

#endif // DWARF_H
