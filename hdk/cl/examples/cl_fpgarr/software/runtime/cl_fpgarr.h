#ifndef CL_FPGARR_H
#define CL_FPGARR_H
#define CL_FPGARR_CSR_BASE 0x100000
#include <stdint.h>
typedef enum {
  BUF_ADDR_HI = 0,      // 0
  BUF_ADDR_LO,          // 1
  BUF_SIZE_HI,          // 2
  BUF_SIZE_LO,          // 3
  WRITE_BUF_UPDATE,     // 4
  READ_BUF_UPDATE,      // 5
  RECORD_FORCE_FINISH,  // 6
  REPLAY_START,         // 7, currently not used
  RR_MODE,              // 8
  RR_RSVD_1,            // 9
  RECORD_BITS_HI,       // 10
  RECORD_BITS_LO,       // 11
  REPLAY_BITS_HI,       // 12
  REPLAY_BITS_LO,       // 13
} rr_csr_enum;
#define RR_CSR_ADDR(idx) (CL_FPGARR_CSR_BASE + 0x4 * idx)
#define UINT64_HI32(x) ((((uint64_t) x) >> 32) & 0xffffffff)
#define UINT64_LO32(x) ( ((uint64_t) x) & 0xffffffff)

extern void init_rr();
extern void do_record_start();
extern void do_record_stop();
extern void do_replay_start();
extern void do_replay_stop();

extern void do_pre_rr();
extern void do_post_rr();

extern uint8_t is_record();
extern uint8_t is_replay();

#endif // CL_FPGARR_H
