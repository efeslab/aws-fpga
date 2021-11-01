#define CL_FPGARR_CSR_BASE 0x100000
typedef enum {
  BUF_ADDR_HI = 0,      // 0
  BUF_ADDR_LO,          // 1
  BUF_SIZE_HI,          // 2
  BUF_SIZE_LO,          // 3
  WRITE_BUF_UPDATE,     // 4
  READ_BUF_UPDATE,      // 5
  RECORD_FORCE_FINISH,  // 6
  REPLAY_START,         // 7, currently not used
  RR_MODE,              // 6
} rr_csr_enum;
#define RR_CSR_ADDR(idx) (CL_FPGARR_CSR_BASE + 0x4 * idx)
