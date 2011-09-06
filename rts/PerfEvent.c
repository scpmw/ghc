
#ifdef USE_PERF_EVENT

#include "Rts.h"

#include "PerfEvent.h"
#include "Task.h"
#include "RtsUtils.h"
#include "Trace.h"

#include <string.h>
#include <sys/types.h>
#include <sys/mman.h>
#include <sys/ioctl.h>

// Linux-specific includes required for perf_events
#include <unistd.h>
#include <sys/syscall.h>
#include <linux/perf_event.h>

// Some parts adapted from perf.h (tools/perf/perf.h in linux kernel tree)
#ifdef i386_HOST_ARCH
#define rmb()		asm volatile("lock; addl $0,0(%%esp)" ::: "memory")
#endif
#ifdef x86_64_HOST_ARCH
#define rmb()		asm volatile("lfence" ::: "memory")
#endif
#ifdef powerpc_HOST_ARCH
#define rmb()		asm volatile ("sync" ::: "memory")
#endif
#ifdef hppa1_1_HOST_ARCH
#define rmb()		asm volatile("" ::: "memory")
#endif
#ifdef sparc_HOST_ARCH
#define rmb()		asm volatile("":::"memory")
#endif
#ifndef rmb
#error perf_event backend does not support this architecture!
#endif

// Number of pages used for capturing perf_events samples.
// Note 1: Must be a power of 2!
// Note 2: The kernel seems to object if we grab too much memory, so
//         having this set too high will cause EPERMs with too many tasks!
#define PERF_EVENT_MMAP_PAGES 32

#ifdef TRACING
static size_t get_page_size(void);
static void perf_event_stream(Task *task);
#endif

static inline int
sys_perf_event_open(struct perf_event_attr *attr,
		      pid_t pid, int cpu, int group_fd,
		      unsigned long flags)
{
	attr->size = sizeof(*attr);
	return syscall(__NR_perf_event_open, attr, pid, cpu,
	               group_fd, flags);
}


#ifdef TRACING
static size_t get_page_size(void)
{
	static size_t page_size = 0;
	if (0 == page_size)
		return page_size = sysconf(_SC_PAGE_SIZE);
	return page_size;
}
#endif

void perf_event_init(Task *task)
{
	// Clear
	task->perf_event_fd = -1;
	task->perf_event_mmap = NULL;
	task->perf_event_last_head = 0;

#ifdef TRACING
	// Enabled?
	if (0 == RtsFlags.PerfEventFlags.sampleType) {
		return;
	}
	
	// Initialize perf_event attributes
	struct perf_event_attr attr;
	memset(&attr, 0, sizeof(attr));
	attr.type = PERF_TYPE_HARDWARE;
	attr.config = PERF_COUNT_HW_CPU_CYCLES;
	attr.sample_period = 100000;
	attr.sample_type = PERF_SAMPLE_IP | PERF_SAMPLE_TID;
	attr.exclude_kernel = 1;
	attr.disabled = 1;

	// Allocate counter
	task->perf_event_fd = sys_perf_event_open(&attr, 0, -1, -1, 0);
	if (task->perf_event_fd < 0) {
		sysErrorBelch("Could not open perf_event");
		return;
	}

	// Test
	StgWord64 val;
	if (read(task->perf_event_fd, &val, sizeof(val)) <= 0) {
		sysErrorBelch("Could not read from perf_event");
		close(task->perf_event_fd);
		task->perf_event_fd = -1;
		return;
	}

	// Associate a memory map
	size_t mmap_length = get_page_size() * (PERF_EVENT_MMAP_PAGES + 1);
	task->perf_event_mmap = 
		mmap(NULL, mmap_length, PROT_READ | PROT_WRITE, MAP_SHARED, task->perf_event_fd, 0);
	if (task->perf_event_mmap == MAP_FAILED) {
		sysErrorBelch("Could not allocate memory-map for perf_event");
		return;
	}

	// Start following the stream
	task->perf_event_last_head = task->perf_event_data->data_head;
	task->perf_event_data->data_tail = task->perf_event_last_head;
#endif

}

#ifdef TRACING
void perf_event_stream(Task *task) {

	// Read new head pointer
	StgWord64 last_head = task->perf_event_last_head;
	StgWord64 new_head = task->perf_event_data->data_head;
	if (last_head >= new_head) return;

	// Write barrier
	rmb();

	// Buffer data
	StgWord64 buf_size = get_page_size() * PERF_EVENT_MMAP_PAGES;
	StgWord64 buf_mask = buf_size - 1; // Assuming page size is a power of 2, obviously.
	StgWord8 *data_base = ((StgWord8 *)task->perf_event_mmap) + get_page_size();
	StgWord8 *data = data_base + (last_head & buf_mask);
	StgBool free_data = 0;

	// Wrap around? Play it safe: Assemble into a new buffer
	if ((last_head & ~buf_mask) != (new_head & ~buf_mask)) {

		StgWord64 bytes_before_wrap = buf_size - (last_head & buf_mask);
		StgWord64 bytes_after_wrap  = new_head & buf_mask;

		//printf("last:%ld new:%ld mask:%ld before:%ld after:%ld\n", last_head, new_head, buf_mask, bytes_before_wrap, bytes_after_wrap);
		StgWord8 *new_data = stgMallocBytes(new_head - last_head, "perf_event_stream wrap buffer");
		memcpy(new_data, data, bytes_before_wrap);
		memcpy(new_data + bytes_before_wrap, data_base, bytes_after_wrap);
		data = new_data;
		free_data = 1;
	}

	// Count number of samples
	StgWord32 n_samples = 0;
	StgWord8 *pos = data;
	StgWord32 hdr_size = sizeof(struct perf_event_header);
	while (pos + hdr_size <= data + (new_head - last_head)) {
		struct perf_event_header *hdr = (struct perf_event_header *) pos;
		if (pos + hdr->size > data + (new_head - last_head)) {
			break;
		}
		if (hdr->type == PERF_RECORD_SAMPLE) {
			n_samples++;
		}
		pos += hdr->size;
	}
	StgWord8 *end_pos = pos;

	//printf("reading %d samples (%ld bytes)...\n", n_samples, end_pos - data);

	// Read samples
	pos = data;
	void **ips = (void **) stgMallocBytes(sizeof(void *) * n_samples, "perf_event_stream samples");
	StgWord32 i = 0;
	while (pos != end_pos) {
		struct perf_event_header *hdr = (struct perf_event_header *) pos;
		if (hdr->type == PERF_RECORD_SAMPLE) {
			ips[i++] = (void *) *((StgWord64 *) (pos + hdr_size));
		}
		pos += hdr->size;
	}

	// Output samples
	traceInstrPtrSample(task->cap, n_samples, ips);
	stgFree(ips);

	// Our final head (for incomplete data we might not have read everyhing!)
	// Note corrupt data might cause us to get stuck here...
	StgWord64 final_head = last_head + (end_pos - data);

	// Free buffer
	if (free_data)
		stgFree(data);

	//printf("new %ld final %ld\n", new_head, final_head);

	// Advance head pointer
	task->perf_event_last_head = final_head;
	task->perf_event_data->data_tail = final_head;
}

#endif // TRACING

void perf_event_start_mutator_count(void)
{
	Task *task = myTask();
	if(!task || task->perf_event_fd == -1) return;	
	ioctl(task->perf_event_fd, PERF_EVENT_IOC_ENABLE);
}

void perf_event_stop_mutator_count(void)
{
	Task *task = myTask();
	if(!task || task->perf_event_fd == -1) return;	
	ioctl(task->perf_event_fd, PERF_EVENT_IOC_DISABLE);
#ifdef TRACING
	perf_event_stream(task);
#endif
}

#endif // USE_PERF_EVENT
