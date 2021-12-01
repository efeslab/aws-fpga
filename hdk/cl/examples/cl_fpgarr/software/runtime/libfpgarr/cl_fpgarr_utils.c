#include <fpga_hugealloc.h>
#ifdef SV_TEST
#include <utils/sh_dpi_tasks.h>
#endif
#include <utils/log.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>
#include <string.h>
#include <stdio.h>
#include <errno.h>

#include "cl_fpgarr_utils.h"
#include "cl_fpgarr_csrs.h"
#include "cl_fpgarr_cfg.h"

// pa is not used in software simulation
uint8_t *rr_alloc_buffer(uint64_t size, uint64_t *pa) {
#ifdef SV_TEST
    uint8_t *va;
    va = aligned_alloc(BUFFER_ALIGNMENT, size);
    assert(va != NULL);
    return va;
#else
    void *va;
    uint64_t sizeB;
    assert(fpga_hugealloc_get(&va, pa, &sizeB) == 0);
    assert(size <= sizeB);
    memset(va, 0, sizeB);
    log_info("rr_alloc_buffer, va %p, pa %p, size %ld\n", va, (void *)(*pa),
             sizeB);
    return (uint8_t *)(va);
#endif
}

uint8_t *rr_alloc_setup_buffer(uint64_t size, uint64_t buf_update_csr) {
    uint64_t pa;
    uint8_t *va = rr_alloc_buffer(size, &pa);
#ifdef SV_TEST
    setup_buffer(va, size, buf_update_csr);
    return va;
#else
    setup_buffer((uint8_t*)(pa), size, buf_update_csr);
    return (uint8_t *)(va);
#endif
}

void rr_dealloc_buffer(uint8_t *buf) {
#ifdef SV_TEST
    free(buf);
#else
    fpga_hugealloc_put((void*)buf);
#endif
}

// in simulation, the unit is passed to sv_pause
// on real hardware, the unit is 100000us (100ms)
void rr_wait(uint32_t unit) {
#ifdef SV_TEST
    sv_pause(unit);
#else
    usleep(unit*100000);
#endif
}

void dump_trace(const char *msg, const char *filename, uint8_t *p,
                       uint64_t size_bits) {
    int size_bytes = (size_bits + 7) / 8;
    // print trace to stdout
    printf("%s: size %ld bits (%d B)\n", msg, size_bits, size_bytes);
#ifdef DUMP_TRACE_TXT
    printf("%s: Trace Dump:\n", msg);
    for (int i = 0; i < size_bytes; ++i) {
        // put 1-byte a time
        printf("%02x", p[i]);
        if (i % 64 == 63) {
            printf("\n");
        } else if (i % 8 == 7) {
            printf(" ");
        } else if (i % 4 == 3) {
            printf("_");
        }
    }
    putchar('\n');
#endif
    if (size_bytes) {
        unlink(filename);
        errno = 0; // suppress log_info
        // save trace to file
        int fd = open(filename, O_RDWR | O_CREAT,
                      S_IRUSR | S_IWUSR | S_IRGRP | S_IWGRP | S_IROTH);
        write(fd, &size_bits, TRACE_LEN_BYTES);
        write(fd, p, size_bytes);
        fsync(fd);
        close(fd);
    } else
        log_warning("Empty trace %s, will not save to file", filename);
}

