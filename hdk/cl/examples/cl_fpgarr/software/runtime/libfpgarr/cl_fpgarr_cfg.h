#ifndef CL_FPGARR_CFG_H
#define CL_FPGARR_CFG_H

#ifdef SV_TEST
// 128 MB
#define DEFAULT_BUFFER_SIZE (1UL << 30)
#define POLLING_INTERVAL 1
#else
#define DEFAULT_BUFFER_SIZE (1ULL << 30)
#define POLLING_INTERVAL 5
#endif
#define BUFFER_ALIGNMENT 4096
#define TRACE_LEN_BYTES 8

// MACRO configuration
#undef DUMP_TRACE_TXT

#endif // CL_FPGARR_CFG_H
