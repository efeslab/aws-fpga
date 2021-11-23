#ifndef CL_FPGARR_H
#define CL_FPGARR_H
#define CL_FPGARR_CSR_BASE 0x100000
#include <stdint.h>

#define RR_CSR_VERSION_INT 20211123
typedef enum {
  BUF_ADDR_HI = 0,           // 0
  BUF_ADDR_LO,               // 1
  BUF_SIZE_HI,               // 2
  BUF_SIZE_LO,               // 3
  RECORD_BUF_UPDATE,         // 4
  REPLAY_BUF_UPDATE,         // 5
  RECORD_FORCE_FINISH,       // 6
  REPLAY_START,              // 7, currently not used
  RR_MODE,                   // 8
  RR_STATE,                  // 9
  RECORD_BITS_HI,            // 10
  RECORD_BITS_LO,            // 11
  REPLAY_BITS_HI,            // 12
  REPLAY_BITS_LO,            // 13
  VALIDATE_BUF_UPDATE,       // 14
  RR_RSVD_2,                 // 15
  VALIDATE_BITS_HI,          // 16
  VALIDATE_BITS_LO,          // 17
  RT_REPLAY_BITS_HI,         // 18
  RT_REPLAY_BITS_LO,         // 19
  RR_CSR_VERSION,            // 20
} rr_csr_enum;

#define RR_CSR_ADDR(idx) (CL_FPGARR_CSR_BASE + 0x4 * idx)
#define UINT64_HI32(x) ((((uint64_t) x) >> 32) & 0xffffffff)
#define UINT64_LO32(x) ( ((uint64_t) x) & 0xffffffff)
#define UINT64_FROM32(hi, lo) ((((uint64_t) hi) << 32) | ((uint64_t) lo))

// 64 MB
#define DEFAULT_BUFFER_SIZE (0x4000000)
#define BUFFER_ALIGNMENT 4096
#define TRACE_LEN_BYTES 8

extern int init_rr(int slot_id);
extern void do_pre_rr();
extern void do_post_rr();

extern uint8_t is_record();
extern uint8_t is_replay();
extern uint8_t is_validate();

#endif // CL_FPGARR_H
