#include <utils/log.h>

#include "cl_fpgarr_csrs.h"
#include "cl_fpgarr_csrs_decode.h"
#include "cl_fpgarr_cfg.h"

#ifndef SV_TEST
pci_bar_handle_t pci_bar1_handle = PCI_BAR_HANDLE_INIT;
#endif

void setup_buffer(uint8_t *p, uint64_t size, uint64_t buf_update_csr) {
    uint32_t trace_buffer_hi, trace_buffer_lo;
    uint32_t trace_buffer_size_hi, trace_buffer_size_lo;
    trace_buffer_hi = UINT64_HI32(p);
    trace_buffer_lo = UINT64_LO32(p);
    trace_buffer_size_hi = UINT64_HI32(size);
    trace_buffer_size_lo = UINT64_LO32(size);
#ifdef SV_TEST
    sv_map_host_memory(p);
#endif
    // configure csrs via rr_cfg_bus
    rr_cfg_poke(BUF_ADDR_HI, trace_buffer_hi);
    rr_cfg_poke(BUF_ADDR_LO, trace_buffer_lo);
    rr_cfg_poke(BUF_SIZE_HI, trace_buffer_size_hi);
    rr_cfg_poke(BUF_SIZE_LO, trace_buffer_size_lo);
    rr_cfg_poke(buf_update_csr, 1);
}

// return the stable counter
// polling a 64-bit CSR counter until it is stable, then force it to finish,
// then wait the counter to be stable again
uint64_t rr_wait_counter_stable(uint64_t lo_csr_idx, uint64_t hi_csr_idx) {
    uint64_t newcnt, oldcnt;
    rr_cfg_peek64(lo_csr_idx, hi_csr_idx, &newcnt);
    do {
        oldcnt = newcnt;
        rr_wait(POLLING_INTERVAL);
        rr_cfg_peek64(lo_csr_idx, hi_csr_idx, &newcnt);
    } while (newcnt != oldcnt);
    return newcnt;
}

/*
 * DBG related
 */
#define LOG_INFO_DBG_CSR_U32(fmt, csr_idx) \
    uint32_t csr_idx##_val; \
    rr_cfg_peek(csr_idx, &(csr_idx##_val)); \
    log_info("DBG: " #csr_idx " = " fmt, csr_idx##_val)
#define LOG_INFO_DBG_CSR_U64(fmt, csr_idx_pfx) \
    uint64_t csr_idx_pfx##_val; \
    rr_cfg_peek64(csr_idx_pfx##_LO, csr_idx_pfx##_HI, &(csr_idx_pfx##_val)); \
    log_info("DBG: " #csr_idx_pfx " = " fmt, csr_idx_pfx##_val)

#ifdef DEBUG_PCHK_CSR
#define LOG_INFO_DBG_CSR_PCHK(pchk_csr_idx) \
    LOG_INFO_DBG_CSR_U32("%#x", pchk_csr_idx##_P0); \
    LOG_INFO_DBG_CSR_U32("%#x", pchk_csr_idx##_P1); \
    LOG_INFO_DBG_CSR_U32("%#x", pchk_csr_idx##_P2); \
    LOG_INFO_DBG_CSR_U32("%#x", pchk_csr_idx##_P3); \
    LOG_INFO_DBG_CSR_U32("%#x", pchk_csr_idx##_P4)
void debug_pcim_pchk() {
    LOG_INFO_DBG_CSR_U32("%#x", RR_PCIM_PCHK_ASSERTED);
    LOG_INFO_DBG_CSR_PCHK(RR_LOGGING_WB_PCHK);
    LOG_INFO_DBG_CSR_PCHK(RR_VALIDATION_WB_PCHK);
    LOG_INFO_DBG_CSR_PCHK(RR_CL_PCIM_PCHK);
    LOG_INFO_DBG_CSR_PCHK(RR_SH_PCIM_PCHK);
}
#endif

void debug_check() {
    // OLD debug csr
    check_rr_state();
    LOG_INFO_DBG_CSR_U32("%#x", RR_TRACE_FIFO_ASSERT);
    LOG_INFO_DBG_CSR_U32("%d", RR_ON_THE_FLY_BALANCE);
#ifdef DEBUG_RECORD_CSR
    // gefei dbg_csr
    LOG_INFO_DBG_CSR_U64("%ld", RR_WB_RECORD_DBG_BITS_NON_ALIGNED);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_FIFO_WR_CNT);

    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcim_R);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_AW);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_W);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_AR);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_AW);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_AW);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_ocl_W);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_AW);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_W);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_B);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_pcis_AR);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_AR);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_sda_W);
    LOG_INFO_DBG_CSR_U32("%d", RR_WB_RECORD_DBG_BITS_CHPKT_CNT_bar1_AR);

    // mjc dbg_csr
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_IN_PKT_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_OUT_PKT_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_IN_BITS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_OUT_BITS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_IN_FIFO_OUT_PKT_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_IN_FIFO_OUT_ORIG_BITS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_RECORD_IN_FIFO_OUT_ALIGNED_BITS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_WB_AW_TRANS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_WB_W_TRANS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RR_WB_B_TRANS_CNT);
    LOG_INFO_DBG_CSR_U64("%ld", RT_RECORD_UNHANDLED_SIZE);
    LOG_INFO_DBG_CSR_U64("%ld", RT_CURRENT_RECORD_UNHANDLED_SIZE);
    LOG_INFO_DBG_CSR_U64("%ld", RT_LEFTOVER_SIZE);
    LOG_INFO_DBG_CSR_U64("%ld", RT_RECORD_CURR);
    dump_trace_rw_axi_status();
#endif // DEBUG_RECORD_CSR
#ifdef DEBUG_REPLAY_CSR
    LOG_INFO_DBG_CSR_U32("%d", RR_REPLAY_AR_TRANS_CNT);
    LOG_INFO_DBG_CSR_U32("%d", RR_REPLAY_R_TRANS_CNT);
    LOG_INFO_DBG_CSR_U32("%d", RR_REPLAY_IN_FIFO_IN_CNT);
    LOG_INFO_DBG_CSR_U32("%d", RR_REPLAY_IN_FIFO_OUT_CNT);
    LOG_INFO_DBG_CSR_U32("%d", RR_REPLAY_OUT_FIFO_IN_CNT);
    LOG_INFO_DBG_CSR_U32("%d", RR_REPLAY_OUT_FIFO_OUT_CNT);
    dump_trace_split_dbg_csr();
#endif // DEBUG_REPLAY_CSR
#ifdef DEBUG_PCHK_CSR
    debug_pcim_pchk();
#endif // DEBUG_PCHK_CSR
}

void check_rr_state() {
    LOG_INFO_DBG_CSR_U64("%#lx", RR_STATE);
}
