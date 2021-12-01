#ifndef CL_FPGARR_CSRS_DECODE_H
#define CL_FPGARR_CSRS_DECODE_H
/*
 * Parse RR_MODE register configuration
 */
typedef union {
    struct {
        uint8_t recordEn : 1;          // bit 0
        uint8_t replayEn : 1;          // bit 1
        uint8_t outputValidateEn : 1;  // bit 2
        uint32_t unused : 29;
    };
    uint32_t val;
} rr_mode_t;
#define RR_MODE_INIT {.val = 0}
#endif // CL_FPGARR_CSRS_DECODE_H
