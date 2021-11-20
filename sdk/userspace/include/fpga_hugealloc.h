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

#ifdef __cplusplus
}
#endif
