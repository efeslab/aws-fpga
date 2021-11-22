#pragma once

#include "hal/fpga_common.h"

#ifdef __cplusplus
extern "C" {
#endif

struct fpga_hugepage_desc {
    void *va;
    uint64_t pa;
};

int fpga_hugealloc_get_all_pages(struct fpga_hugepage_desc **descs);

// return virutal addr, phy addr, size of the hugepage in bytes
int fpga_hugealloc_get(void **va, uint64_t *pa, uint64_t *sizeB);

int fpga_hugealloc_put(void *va);

#ifdef __cplusplus
}
#endif
