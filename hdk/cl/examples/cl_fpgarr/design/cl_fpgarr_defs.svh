`ifndef CL_FPGARR_DEFS
`define CL_FPGARR_DEFS
parameter RECORDER_PIPE_DEPTH=4;
// index allocation of AXI channels
parameter LOGB_AW=0;
parameter LOGB_W=1;
parameter LOGB_AR=2;
parameter LOGB_R=0;
parameter LOGB_B=1;
parameter LOGE_AW=0;
parameter LOGE_W=1;
parameter LOGE_AR=2;
parameter LOGE_B=3;
parameter LOGE_R=4;
// RR_CHANNEL_WIDTH_BITS should be long enough to encode the max amount of
// data to log for a single channel
parameter RR_CHANNEL_WIDTH_BITS=32;

// This is a workaround for vcs non-local function call.
// the function GET_OFFSET should be a constant function bound to a specific
// instance of rr_logging_bus_t
`define DEF_GET_OFFSET(channel_widths)                                         \
  function automatic int GET_OFFSET (int idx);                                 \
     GET_OFFSET = 0;                                                           \
     for (int i=0; i < idx; i=i+1)                                             \
        GET_OFFSET += channel_widths[i];                                       \
  endfunction
`endif
