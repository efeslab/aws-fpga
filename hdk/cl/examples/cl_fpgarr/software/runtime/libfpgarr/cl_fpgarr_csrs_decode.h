#ifndef CL_FPGARR_CSRS_DECODE_H
#define CL_FPGARR_CSRS_DECODE_H
#include <stdint.h>
/*
 * Parse RR_MODE register configuration
 */
typedef union {
    struct {
        uint8_t recordEn : 1;               // bit 0
        uint8_t replayEn : 1;               // bit 1
        uint8_t outputValidateEn : 1;       // bit 2
        uint8_t enable_PCIM_B_buffer : 1;   // bit 3
        uint8_t enable_PCIM_workaround : 1; // bit 4
        uint32_t unused : 26;
    } __attribute__((packed));
    uint32_t val;
} rr_mode_t;
#define RR_MODE_INIT {.val = 0}

typedef union {
    struct {
        uint8_t asm_done : 1;
        uint8_t asm_wait_body : 1;
        uint8_t asm_header : 1;
        uint8_t hi_full : 1;
        uint8_t lo_empty : 1;
        uint8_t lo_header : 1;
        uint8_t lo_body : 1;
        uint8_t lo_replay_done : 1;
        uint16_t lo_remain_len : 16;
        uint32_t rt_replay_axi_cnt : 32;
        uint8_t trace_axi_cnt : 4;
        uint8_t hi_pad_last_oneoff : 1;
        uint8_t hi_pad_last : 1;
        uint8_t hi_lo_shift : 1;
        uint8_t lo_valid_off : 8;
        uint32_t replay_axi_total : 32;
    } __attribute__((packed));
    uint32_t val[4];
} trace_split_dbg_csr_t;
void dump_trace_split_dbg_csr();

typedef union {
    struct {
        uint16_t bid : 16;
        uint16_t awid : 16;
        uint8_t bvalid : 1;
        uint8_t bready : 1;
        uint8_t wvalid : 1;
        uint8_t wready : 1;
        uint8_t awvalid : 1;
        uint8_t awready : 1;
        uint8_t arvalid : 1;
        uint8_t arready : 1;
        uint8_t rvalid : 1;
        uint8_t rready : 1;
    } __attribute__((packed));
    uint32_t val[2];
} trace_rw_axi_status_t;
void dump_trace_rw_axi_status();
#endif // CL_FPGARR_CSRS_DECODE_H
