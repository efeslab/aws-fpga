#ifndef CL_FPGARR_UTILS_H
#define CL_FPGARR_UTILS_H
#include <stdint.h>
#include <time.h>

#define UINT64_HI32(x) ((((uint64_t) x) >> 32) & 0xffffffff)
#define UINT64_LO32(x) ( ((uint64_t) x) & 0xffffffff)
#define UINT64_FROM32(hi, lo) ((((uint64_t) hi) << 32) | ((uint64_t) lo))

uint8_t *rr_alloc_buffer(uint64_t size, uint64_t *pa);
uint8_t *rr_alloc_setup_buffer(uint64_t size, uint64_t buf_update_csr);
void rr_dealloc_buffer(uint8_t *buf);
void rr_wait(uint32_t unit);

void dump_trace(const char *msg, const char *filename, uint8_t *p,
                       uint64_t size_bits);
static inline void timespec_sub(struct timespec *start, struct timespec *end,
    struct timespec *result) {
  result->tv_nsec = end->tv_nsec - start->tv_nsec;
    result->tv_sec = end->tv_sec - start->tv_sec;
  if (result->tv_nsec < 0) {
    result->tv_nsec += 1000000000L;
    result->tv_sec -= 1;
  }
}
#endif // CL_FPGARR_UTILS_H
