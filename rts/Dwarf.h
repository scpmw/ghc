
#ifndef DWARF_H
#define DWARF_H

#include "BeginPrivate.h"

#ifdef USE_DWARF

#include "Hash.h"

typedef struct DwarfUnit_ DwarfUnit;
typedef struct DwarfProc_ DwarfProc;
typedef enum DwarfSource_ DwarfSource;
typedef struct DebugInfo_ DebugInfo;

struct DwarfUnit_ {
	char *name;
	char *comp_dir;
	void *low_pc, *high_pc;
	StgWord8 *debug_data;
	DwarfProc *procs;
	StgWord proc_count;
	StgWord16 max_proc_id;

	HashTable *proc_table; // by name
	DwarfProc **procs_by_id; // by id
	DwarfProc **procs_by_pc; // by low_pc

	DwarfUnit *next;
};

enum DwarfSource_ {
	DwarfSourceDwarf,
	DwarfSourceDwarfBlock,
	DwarfSourceSymtab,
};

struct DwarfProc_ {
	char *name;
	StgWord16 id;
	StgWord16 parent_id;
	void *low_pc;
	void *high_pc;
	StgWord8 *debug_data;
	DwarfSource source;
	struct DwarfProc_ *next;
};

extern DwarfUnit *dwarf_units;

void dwarf_load(void);
DwarfUnit *dwarf_get_unit(char *name);
DwarfProc *dwarf_get_proc(DwarfUnit *unit, char *name);
void dwarf_free(void);

void dwarf_init_lookup(void);
DwarfProc *dwarf_lookup_proc(void *ip, DwarfUnit **unit);

struct DebugInfo_ {
	StgWord16 sline, scol, eline, ecol;
	char *file;
	char *name;
	StgWord depth;
};

StgWord dwarf_get_debug_info(DwarfUnit *unit, DwarfProc *proc, DebugInfo *infos, StgWord max_infos);

#endif // USE_DWARF

#include "EndPrivate.h"

#endif // DWARF_H
