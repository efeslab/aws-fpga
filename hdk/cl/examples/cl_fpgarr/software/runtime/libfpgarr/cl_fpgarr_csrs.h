#ifndef CL_FPGARR_CSRS_H
#define CL_FPGARR_CSRS_H
#include <stdint.h>
#include <assert.h>

#ifdef SV_TEST
//#include <fpga_pci_sv.h>
#include <utils/sh_dpi_tasks.h>
#else
#include <fpga_pci.h>
extern pci_bar_handle_t pci_bar1_handle;
#endif

#include "cl_fpgarr_utils.h"

#define CL_FPGARR_CSR_BASE 0x100000
#define RR_CSR_VERSION_INT 2021120605
// DEBUG CSR config
#undef DEBUG_RECORD_CSR
#undef DEBUG_PCHK_CSR
#undef DEBUG_REPLAY_CSR
typedef enum {
  BUF_ADDR_HI = 0,           // 0
  BUF_ADDR_LO,               // 1
  BUF_SIZE_HI,               // 2
  BUF_SIZE_LO,               // 3
  RECORD_BUF_UPDATE,         // 4
  REPLAY_BUF_UPDATE,         // 5
  RECORD_FORCE_FINISH,       // 6
  REPLAY_START,              // 7
  RR_MODE,                   // 8
  RR_STATE_LO,               // 9
  RECORD_BITS_HI,            // 10
  RECORD_BITS_LO,            // 11
  REPLAY_BITS_HI,            // 12
  REPLAY_BITS_LO,            // 13
  VALIDATE_BUF_UPDATE,       // 14
  RR_STATE_HI,               // 15
  VALIDATE_BITS_HI,          // 16
  VALIDATE_BITS_LO,          // 17
  RT_REPLAY_BITS_HI,         // 18
  RT_REPLAY_BITS_LO,         // 19
  RR_TRACE_FIFO_ASSERT,      // 20
  RR_CSR_VERSION,            // 21
  RR_ON_THE_FLY_BALANCE,     // 22
  INT_BUF_UPDATE,            // 23
#ifdef DEBUG_RECORD_CSR
  // gefei dbg_csr
  RR_WB_RECORD_DBG_BITS_NON_ALIGNED_HI,
  RR_WB_RECORD_DBG_BITS_NON_ALIGNED_LO,
  RR_WB_RECORD_DBG_BITS_FIFO_WR_CNT,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcim_R,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_AW,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_W,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_AR,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_AW,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_AW,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_W,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_AW,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_W,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_B,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_AR,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_AR,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_W,
  RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_AR,
  // mjc dbg_csr
  RR_RECORD_IN_PKT_CNT_HI,
  RR_RECORD_IN_PKT_CNT_LO,
  RR_RECORD_OUT_PKT_CNT_HI,
  RR_RECORD_OUT_PKT_CNT_LO,
  RR_RECORD_IN_BITS_CNT_HI,
  RR_RECORD_IN_BITS_CNT_LO,
  RR_RECORD_OUT_BITS_CNT_HI,
  RR_RECORD_OUT_BITS_CNT_LO,
  RR_RECORD_IN_FIFO_OUT_PKT_CNT_HI,
  RR_RECORD_IN_FIFO_OUT_PKT_CNT_LO,
  RR_RECORD_IN_FIFO_OUT_ORIG_BITS_CNT_HI,
  RR_RECORD_IN_FIFO_OUT_ORIG_BITS_CNT_LO,
  RR_RECORD_IN_FIFO_OUT_ALIGNED_BITS_CNT_HI,
  RR_RECORD_IN_FIFO_OUT_ALIGNED_BITS_CNT_LO,
  RR_WB_AW_TRANS_CNT_HI,
  RR_WB_AW_TRANS_CNT_LO,
  RR_WB_W_TRANS_CNT_HI,
  RR_WB_W_TRANS_CNT_LO,
  RR_WB_B_TRANS_CNT_HI,
  RR_WB_B_TRANS_CNT_LO,
  RT_RECORD_UNHANDLED_SIZE_HI,
  RT_RECORD_UNHANDLED_SIZE_LO,
  RT_CURRENT_RECORD_UNHANDLED_SIZE_HI,
  RT_CURRENT_RECORD_UNHANDLED_SIZE_LO,
  RT_LEFTOVER_SIZE_HI,
  RT_LEFTOVER_SIZE_LO,
  RT_RECORD_CURR_HI,
  RT_RECORD_CURR_LO,
  RR_AXI_STATUS_HI,
  RR_AXI_STATUS_LO,
#endif // DEBUG_RECORD_CSR
#ifdef DEBUG_PCHK_CSR
  // pcim pchk csrs
  RR_PCIM_PCHK_ASSERTED,
  RR_LOGGING_WB_PCHK_P0,
  RR_LOGGING_WB_PCHK_P1,
  RR_LOGGING_WB_PCHK_P2,
  RR_LOGGING_WB_PCHK_P3,
  RR_LOGGING_WB_PCHK_P4,
  RR_VALIDATION_WB_PCHK_P0,
  RR_VALIDATION_WB_PCHK_P1,
  RR_VALIDATION_WB_PCHK_P2,
  RR_VALIDATION_WB_PCHK_P3,
  RR_VALIDATION_WB_PCHK_P4,
  RR_CL_PCIM_PCHK_P0,
  RR_CL_PCIM_PCHK_P1,
  RR_CL_PCIM_PCHK_P2,
  RR_CL_PCIM_PCHK_P3,
  RR_CL_PCIM_PCHK_P4,
  RR_SH_PCIM_PCHK_P0,
  RR_SH_PCIM_PCHK_P1,
  RR_SH_PCIM_PCHK_P2,
  RR_SH_PCIM_PCHK_P3,
  RR_SH_PCIM_PCHK_P4,
#endif // DEBUG_PCHK_CSR
#ifdef DEBUG_REPLAY_CSR
  RR_REPLAY_AR_TRANS_CNT,
  RR_REPLAY_R_TRANS_CNT,
  RR_REPLAY_IN_FIFO_IN_CNT,
  RR_REPLAY_IN_FIFO_OUT_CNT,
  RR_REPLAY_OUT_FIFO_IN_CNT,
  RR_REPLAY_OUT_FIFO_OUT_CNT,
  RR_TRACE_SPLIT_DBG_CSR_P0,
  RR_TRACE_SPLIT_DBG_CSR_P1,
  RR_TRACE_SPLIT_DBG_CSR_P2,
  RR_TRACE_SPLIT_DBG_CSR_P3,
#endif // DEBUG_REPLAY_CSR
} rr_csr_enum;

#define RR_CSR_ADDR(idx) (CL_FPGARR_CSR_BASE + 0x4 * idx)

static inline int rr_cfg_poke(uint64_t csr_idx, uint32_t value) {
#ifdef SV_TEST
    cl_poke_bar1(RR_CSR_ADDR(csr_idx), value);
    return 0;
#else
    assert(pci_bar1_handle != PCI_BAR_HANDLE_INIT);
    return fpga_pci_poke(pci_bar1_handle, RR_CSR_ADDR(csr_idx), value);
#endif
}

static inline int rr_cfg_peek(uint64_t csr_idx, uint32_t *value) {
#ifdef SV_TEST
    cl_peek_bar1(RR_CSR_ADDR(csr_idx), value);
    return 0;
#else
    assert(pci_bar1_handle != PCI_BAR_HANDLE_INIT);
    return fpga_pci_peek(pci_bar1_handle, RR_CSR_ADDR(csr_idx), value);
#endif
}

// TODO: There is a fpga_pci_peek64 but I haven't tested it.
static inline int rr_cfg_peek64(uint64_t lo_csr_idx, uint64_t hi_csr_idx,
                                uint64_t *value) {
    uint32_t lo, hi;
    int rc = 0;
    rc |= rr_cfg_peek(lo_csr_idx, &lo);
    rc |= rr_cfg_peek(hi_csr_idx, &hi);
    *value = UINT64_FROM32(hi, lo);
    return rc;
}

extern void setup_buffer(uint8_t *p, uint64_t size, uint64_t buf_update_csr);
extern uint64_t rr_wait_counter_stable(uint64_t lo_csr_idx, uint64_t hi_csr_idx);

extern void debug_check();
extern void check_rr_state();
#endif // CL_FPGARR_CSRS_H
