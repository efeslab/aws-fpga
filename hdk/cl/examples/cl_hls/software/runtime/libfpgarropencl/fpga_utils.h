#ifndef LIBFPGARROPENCL_FPGA_UTILS_H
#define LIBFPGARROPENCL_FPGA_UTILS_H
#include <stdint.h>
#include <stdio.h>
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

#undef log_error
#define log_error(...)          \
  fprintf(stderr, __VA_ARGS__); \
  fputc('\n', stderr)

#undef log_info
#ifdef DEBUG_FPGARROPENCL
#define log_info(...)           \
  fprintf(stdout, __VA_ARGS__); \
  fputc('\n', stdout)
#else
#define log_info(...)
#endif  // DEBUG_FPGARROPENCL

#define errcode_is(ERR) \
  if (errcode_ret) *errcode_ret = ERR
#undef fail_on_errret
#undef fail_on
#define fail_on_errret(is_fail, label, errcode, ...) \
  if (is_fail) {                                     \
    errcode_is(errcode);                             \
    log_error(__VA_ARGS__);                          \
    goto label;                                      \
  }
#define fail_on(is_fail, label, ...) \
  if (is_fail) {                     \
    log_error(__VA_ARGS__);          \
    goto label;                      \
  }
#undef min
#define min(x, y) ((x < y) ? x : y)
#endif  // LIBFPGARROPENCL_FPGA_UTILS_H
