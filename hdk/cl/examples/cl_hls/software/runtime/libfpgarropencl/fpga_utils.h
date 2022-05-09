#ifndef LIBFPGARROPENCL_FPGA_UTILS_H
#define LIBFPGARROPENCL_FPGA_UTILS_H
#include <stdint.h>
#include <time.h>

#include "cl_structs.h"
extern int check_slot_config(int slot_id);
extern int do_dma_write(struct _cl_context *cxt, const void *host_buffer, size_t size,
                        uint64_t address);
extern int do_dma_read(struct _cl_context *cxt, void *host_buffer, size_t size,
                       uint64_t address);
extern void peek_ocl(struct _cl_context *cxt, uint64_t addr, uint32_t *data);
extern void peek_ocl64(struct _cl_context *cxt, uint64_t addr, uint64_t *data);
extern void poke_ocl(struct _cl_context *cxt, uint64_t addr, uint32_t data);
extern void poke_ocl64(struct _cl_context *cxt, uint64_t addr, uint64_t data);
extern void wait_task_complete();
static inline cl_ulong getWallTimens() {
  struct timespec tp;
  clock_gettime(CLOCK_MONOTONIC, &tp);
  return tp.tv_sec * 1000000000 + tp.tv_nsec;
}
#endif  // LIBFPGARROPENCL_FPGA_UTILS_H
