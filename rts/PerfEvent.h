
#ifndef PERF_EVENT_H
#define PERF_EVENT_H

#include "BeginPrivate.h"

#include "Task.h"

void perf_event_init(Task *task);

void perf_event_start_mutator_count(void);
void perf_event_stop_mutator_count(void);

#include "EndPrivate.h"

#endif // PERF_EVENT_H
