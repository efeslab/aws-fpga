#ifndef CL_FPGARR_CFG_H
#define CL_FPGARR_CFG_H

#ifdef SV_TEST
// 128 MB
#define DEFAULT_BUFFER_SIZE (1UL << 30)
  // note: if using AXI_MEMORY_MODEL, this number should be large
  // if use the accurate but slow memory model, this number should be small
  #ifndef RR_POLLING_INTERVAL
    #define RR_POLLING_INTERVAL 1
  #endif
#else
#define DEFAULT_BUFFER_SIZE (1ULL << 30)
  #ifndef RR_POLLING_INTERVAL
    #define RR_POLLING_INTERVAL 5
  #endif
#endif
#define BUFFER_ALIGNMENT 4096
#define TRACE_LEN_BYTES 8

// MACRO configuration
#undef DUMP_TRACE_TXT

#endif // CL_FPGARR_CFG_H
