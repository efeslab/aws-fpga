#pragma once

#include <errno.h>

#include "fpga_hugealloc.h"

#define HUGE_PAGE_PATH "/sys/kernel/mm/hugepages"
#define HUGE_PAGE_1G_PATH HUGE_PAGE_PATH"/hugepages-1048576kB"
#define HUGE_PAGE_2M_PATH HUGE_PAGE_PATH"/hugepages-2048kB"
#define HUGE_PAGE_1G_AVAIL_PATH HUGE_PAGE_1G_PATH"/free_hugepages"
#define HUGE_PAGE_2M_AVAIL_PATH HUGE_PAGE_2M_PATH"/free_hugepages"

#define PAGEMAP_PATH "/proc/self/pagemap"

#define SIZE_1G (1*1024*1024*1024)
#define SIZE_2M (2*1024*1024)

// HUGE PAGE SIZE SELECTION
#define USE_HUGE_1GB
#undef USE_HUGE_2MB

#ifdef USE_HUGE_1GB
#define HUGE_SIZE SIZE_1G
#define MMAP_HUGE_FLAGS MAP_HUGETLB | MAP_HUGE_1GB
#elif USE_HUGE_2MB
#define HUGE_SIZE SIZE_2M
#define MMAP_HUGE_FLAGS MAP_HUGETLB | MAP_HUGE_2MB
#endif

#define PAGE_SHIFT 12

struct pagemap_entry {
    uint64_t pfn : 55;
    uint64_t soft_dirty : 1;
    uint64_t mapped : 1;
    uint64_t zero : 4;
    uint64_t file_page : 1;
    uint64_t swapped : 1;
    uint64_t present : 1;
};
