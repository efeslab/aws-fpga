`ifndef CL_FPGARR_DEFS
`define CL_FPGARR_DEFS
parameter RECORDER_PIPE_DEPTH=4;
parameter MERGETREE_OUT_QUEUE_NSTAGES=2;
parameter REPLAYER_PIPE_DEPTH=4;
parameter CSR_PIPE_DEPTH=2;
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
`define DEF_GET_OFFSET(fname, channel_widths)                                  \
  function automatic int fname (int idx);                                      \
     fname = 0;                                                           \
     for (int i=0; i < idx; i=i+1)                                             \
        fname += channel_widths[i];                                       \
  endfunction

// This is to reuse the function definition of getting the sum of a certain
// range of a parameter array.
// fname: function name
// aname: array name
// idx_b: the index to begin sum
// idx_e: the index to end sum (non-inclusive, i.e. sum of [idx_b..idx_e))
`define DEF_SUM_WIDTH(fname, aname, idx_b, idx_e)                              \
  function automatic int fname;                                                \
   fname = 0;                                                                  \
   for (int i=idx_b; i < idx_e; i=i+1)                                         \
      fname += aname[i];                                                       \
  endfunction

// This is to reuse the function definition of getting the total length of
// a logging unit (fixed-length logb plus loge, and variable-length logb data)
// This is mainly used to parse one logging unit at a time from the backend
// storage This helper function can tell how long a logging unit is.
//
// This function decodes the valid bitmap of logb_valid and aims to finish
// LOGB_CHANNEL_CNT constant additions in a cycle.
`define DEF_GET_LEN(fname, LOGB_CHANNEL_CNT, OFFSET_WIDTH, CHANNEL_WIDTHS)     \
function automatic [OFFSET_WIDTH-1:0] fname                                    \
  (logic [LOGB_CHANNEL_CNT-1:0] logb_bitmap);                                  \
  fname = LOGB_CHANNEL_CNT + LOGE_CHANNEL_CNT;                                 \
  for (int i=0; i < LOGB_CHANNEL_CNT; i=i+1)                                   \
    if (logb_bitmap[i])                                                        \
      fname += OFFSET_WIDTH'(CHANNEL_WIDTHS[i]);                               \
endfunction

// macro utility to connect verilog wire signals to systemverilog interfaces
// b for bus, m for master, s for slave
// bus signals are accessed via `b.Xvalid`
// wire signals are accessed via name concatenation of m, s, pfx and field names
// pfx is prefix
// TODO: seperate rr axi bus definition and remove wid
// TODO: pcis Xid is just 6bit
`define AXI_MSTR_WIRE2BUS(b, m, s, pfx)                                        \
  rr_axi_bus_t b();                                                            \
  assign b.awid = m``_``s``pfx``awid;                                          \
  assign b.awaddr = m``_``s``pfx``awaddr;                                      \
  assign b.awlen = m``_``s``pfx``awlen;                                        \
  assign b.awsize = m``_``s``pfx``awsize;                                      \
  assign b.awvalid = m``_``s``pfx``awvalid;                                    \
  assign s``_``m``pfx``awready = b.awready;                                    \
                                                                               \
  assign b.wid = 0;  /*TODO: get rid of wid*/                                  \
  assign b.wdata = m``_``s``pfx``wdata;                                        \
  assign b.wstrb = m``_``s``pfx``wstrb;                                        \
  assign b.wlast = m``_``s``pfx``wlast;                                        \
  assign b.wvalid = m``_``s``pfx``wvalid;                                      \
  assign s``_``m``pfx``wready = b.wready;                                      \
                                                                               \
  assign s``_``m``pfx``bid = b.bid;                                            \
  assign s``_``m``pfx``bresp = b.bresp;                                        \
  assign s``_``m``pfx``bvalid = b.bvalid;                                      \
  assign b.bready = m``_``s``pfx``bready;                                      \
                                                                               \
  assign b.arid = m``_``s``pfx``arid;                                          \
  assign b.araddr = m``_``s``pfx``araddr;                                      \
  assign b.arlen = m``_``s``pfx``arlen;                                        \
  assign b.arsize = m``_``s``pfx``arsize;                                      \
  assign b.arvalid = m``_``s``pfx``arvalid;                                    \
  assign s``_``m``pfx``arready = b.arready;                                    \
                                                                               \
  assign s``_``m``pfx``rid = b.rid;                                            \
  assign s``_``m``pfx``rdata = b.rdata;                                        \
  assign s``_``m``pfx``rresp = b.rresp;                                        \
  assign s``_``m``pfx``rlast = b.rlast;                                        \
  assign s``_``m``pfx``rvalid = b.rvalid;                                      \
  assign b.rready = m``_``s``pfx``rready
`define AXI_SLV_WIRE2BUS(b, m, s, pfx)                                         \
  rr_axi_bus_t b();                                                            \
  assign m``_``s``pfx``awid = b.awid;                                          \
  assign m``_``s``pfx``awaddr = b.awaddr;                                      \
  assign m``_``s``pfx``awlen = b.awlen;                                        \
  assign m``_``s``pfx``awsize = b.awsize;                                      \
  assign m``_``s``pfx``awvalid = b.awvalid;                                    \
  assign b.awready = s``_``m``pfx``awready;                                    \
                                                                               \
  /*assign b.wid = 0;  TODO: get rid of wid*/                                  \
  assign m``_``s``pfx``wdata = b.wdata;                                        \
  assign m``_``s``pfx``wstrb = b.wstrb;                                        \
  assign m``_``s``pfx``wlast = b.wlast;                                        \
  assign m``_``s``pfx``wvalid = b.wvalid;                                      \
  assign b.wready = s``_``m``pfx``wready;                                      \
                                                                               \
  assign b.bid = s``_``m``pfx``bid;                                            \
  assign b.bresp = s``_``m``pfx``bresp;                                        \
  assign b.bvalid = s``_``m``pfx``bvalid;                                      \
  assign m``_``s``pfx``bready = b.bready;                                      \
                                                                               \
  assign m``_``s``pfx``arid = b.arid;                                          \
  assign m``_``s``pfx``araddr = b.araddr;                                      \
  assign m``_``s``pfx``arlen = b.arlen;                                        \
  assign m``_``s``pfx``arsize = b.arsize;                                      \
  assign m``_``s``pfx``arvalid = b.arvalid;                                    \
  assign b.arready = s``_``m``pfx``arready;                                    \
                                                                               \
  assign b.rid = s``_``m``pfx``rid;                                            \
  assign b.rdata = s``_``m``pfx``rdata;                                        \
  assign b.rresp = s``_``m``pfx``rresp;                                        \
  assign b.rlast = s``_``m``pfx``rlast;                                        \
  assign b.rvalid = s``_``m``pfx``rvalid;                                      \
  assign m``_``s``pfx``rready = b.rready
`define AXIL_MSTR_WIRE2BUS(b, m, s, pfx)                                       \
  rr_axi_lite_bus_t b();                                                       \
  assign b.awaddr = m``_``s``pfx``awaddr;                                      \
  assign b.awvalid = m``_``s``pfx``awvalid;                                    \
  assign s``_``m``pfx``awready = b.awready;                                    \
                                                                               \
  assign b.wdata = m``_``s``pfx``wdata;                                        \
  assign b.wstrb = m``_``s``pfx``wstrb;                                        \
  assign b.wvalid = m``_``s``pfx``wvalid;                                      \
  assign s``_``m``pfx``wready = b.wready;                                      \
                                                                               \
  assign s``_``m``pfx``bresp = b.bresp;                                        \
  assign s``_``m``pfx``bvalid = b.bvalid;                                      \
  assign b.bready = m``_``s``pfx``bready;                                      \
                                                                               \
  assign b.araddr = m``_``s``pfx``araddr;                                      \
  assign b.arvalid = m``_``s``pfx``arvalid;                                    \
  assign s``_``m``pfx``arready = b.arready;                                    \
                                                                               \
  assign s``_``m``pfx``rdata = b.rdata;                                        \
  assign s``_``m``pfx``rresp = b.rresp;                                        \
  assign s``_``m``pfx``rvalid = b.rvalid;                                      \
  assign b.rready = m``_``s``pfx``rready
`define AXIL_SLV_WIRE2BUS(b, m, s, pfx)                                        \
  rr_axi_lite_bus_t b();                                                       \
  assign m``_``s``pfx``awaddr = b.awaddr;                                      \
  assign m``_``s``pfx``awvalid = b.awvalid;                                    \
  assign b.awready = s``_``m``pfx``awready;                                    \
                                                                               \
  assign m``_``s``pfx``wdata = b.wdata;                                        \
  assign m``_``s``pfx``wstrb = b.wstrb;                                        \
  assign m``_``s``pfx``wvalid = b.wvalid;                                      \
  assign b.wready = s``_``m``pfx``wready;                                      \
                                                                               \
  assign b.bresp = s``_``m``pfx``bresp;                                        \
  assign b.bvalid = s``_``m``pfx``bvalid;                                      \
  assign m``_``s``pfx``bready = b.bready;                                      \
                                                                               \
  assign m``_``s``pfx``araddr = b.araddr;                                      \
  assign m``_``s``pfx``arvalid = b.arvalid;                                    \
  assign b.arready = s``_``m``pfx``arready;                                    \
                                                                               \
  assign b.rdata = s``_``m``pfx``rdata;                                        \
  assign b.rresp = s``_``m``pfx``rresp;                                        \
  assign b.rvalid = s``_``m``pfx``rvalid;                                      \
  assign m``_``s``pfx``rready = b.rready
`define AXI_CONNECT_BUS2WIRE(b, m, s, pfx)                                     \
  .m``_``s``pfx``awid(b.awid),                                                 \
  .m``_``s``pfx``awaddr(b.awaddr),                                             \
  .m``_``s``pfx``awlen(b.awlen),                                               \
  .m``_``s``pfx``awsize(b.awsize),                                             \
  .m``_``s``pfx``awvalid(b.awvalid),                                           \
  .s``_``m``pfx``awready(b.awready),                                           \
                                                                               \
  /*assign b.wid = 0; wid is skipped*/                                         \
  .m``_``s``pfx``wdata(b.wdata),                                               \
  .m``_``s``pfx``wstrb(b.wstrb),                                               \
  .m``_``s``pfx``wlast(b.wlast),                                               \
  .m``_``s``pfx``wvalid(b.wvalid),                                             \
  .s``_``m``pfx``wready(b.wready),                                             \
                                                                               \
  .s``_``m``pfx``bid(b.bid),                                                   \
  .s``_``m``pfx``bresp(b.bresp),                                               \
  .s``_``m``pfx``bvalid(b.bvalid),                                             \
  .m``_``s``pfx``bready(b.bready),                                             \
                                                                               \
  .m``_``s``pfx``arid(b.arid),                                                 \
  .m``_``s``pfx``araddr(b.araddr),                                             \
  .m``_``s``pfx``arlen(b.arlen),                                               \
  .m``_``s``pfx``arsize(b.arsize),                                             \
  .m``_``s``pfx``arvalid(b.arvalid),                                           \
  .s``_``m``pfx``arready(b.arready),                                           \
                                                                               \
  .s``_``m``pfx``rid(b.rid),                                                   \
  .s``_``m``pfx``rdata(b.rdata),                                               \
  .s``_``m``pfx``rresp(b.rresp),                                               \
  .s``_``m``pfx``rlast(b.rlast),                                               \
  .s``_``m``pfx``rvalid(b.rvalid),                                             \
  .m``_``s``pfx``rready(b.rready)

`define AXIL_CONNECT_BUS2WIRE(b, m, s, pfx)                                    \
  .m``_``s``pfx``awaddr(b.awaddr),                                             \
  .m``_``s``pfx``awvalid(b.awvalid),                                           \
  .s``_``m``pfx``awready(b.awready),                                           \
                                                                               \
  .m``_``s``pfx``wdata(b.wdata),                                               \
  .m``_``s``pfx``wstrb(b.wstrb),                                               \
  .m``_``s``pfx``wvalid(b.wvalid),                                             \
  .s``_``m``pfx``wready(b.wready),                                             \
                                                                               \
  .s``_``m``pfx``bresp(b.bresp),                                               \
  .s``_``m``pfx``bvalid(b.bvalid),                                             \
  .m``_``s``pfx``bready(b.bready),                                             \
                                                                               \
  .m``_``s``pfx``araddr(b.araddr),                                             \
  .m``_``s``pfx``arvalid(b.arvalid),                                           \
  .s``_``m``pfx``arready(b.arready),                                           \
                                                                               \
  .s``_``m``pfx``rdata(b.rdata),                                               \
  .s``_``m``pfx``rresp(b.rresp),                                               \
  .s``_``m``pfx``rvalid(b.rvalid),                                             \
  .m``_``s``pfx``rready(b.rready)

// RR CSRS

////////////////////////////////////////////////////////////////////////////////
// !!!!!!!!!!!!!!!!!!!!!!!! ATTENTION !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
// ALWAYS update (increase) this RR_CSR_VERSION_INT after making changes to CSR
// address allocation
parameter int RR_CSR_VERSION_INT = 20211105;
////////////////////////////////////////////////////////////////////////////////
parameter int RR_CSR_CNT = 32;
parameter int RR_CSR_ADDR_WIDTH = $clog2(RR_CSR_CNT);
typedef enum bit [RR_CSR_ADDR_WIDTH-1:0] {
  // BUF_ADDR and BUF_SIZE are the address and size of a buffer in CPU-side
  // memory. The address should be physical addresses. To tell the writeback
  // module about a new buffer, the software need to write the address and
  // size of the buffer to BUF_ADDR and BUF_SIZE, and write 1 to one of the
  // *_BUF_UPDATE registers.
  BUF_ADDR_HI,              // 0
  BUF_ADDR_LO,              // 1
  BUF_SIZE_HI,              // 2
  BUF_SIZE_LO,              // 3
  RECORD_BUF_UPDATE,        // 4
  REPLAY_BUF_UPDATE,        // 5
  // Software needs to write 1 to RECORD_FORCE_FINISH after the computation
  // is done. Writing to this CSR would flush the last packet to the memory.
  // Before writing this CSR, it's recommanded for the software to sleep for
  // a few microseconds.
  RECORD_FORCE_FINISH,      // 6
  REPLAY_START,             // 7, currently not used
  RR_MODE,                  // 8
  RR_RSVD_1,                // 9, 4 bytes reserved to align RECORD_BITS
  // *_BITS are used to tell how many bits is recorded or needs to be replayed.
  // Software need to write this before replay, and read it back after record.
  RECORD_BITS_HI,           // 10
  RECORD_BITS_LO,           // 11
  REPLAY_BITS_HI,           // 12
  REPLAY_BITS_LO,           // 13
  VALIDATE_BUF_UPDATE,      // 14
  RR_RSVD_2,                // 15, 4 bytes recerved to align VALIDATE_BITS
  VALIDATE_BITS_HI,         // 16
  VALIDATE_BITS_LO,         // 17
  RR_CSR_VERSION,           // 18
  RR_CSR_LAST_DONT_USE = RR_CSR_CNT - 1
} rr_csr_enum;
`define RR_CSR_ADDR(idx) (idx << 2)

// PLACEMENT_VEC for runtime loge_valid crossbar
// From aws-fpga doc:
//   MID SLR:
//       CL_SH_DDR
//       BAR1
//       PCIM
//   BOTTOM SLR:
//       PCIS
//       OCL
//       DDR STAT3
//   MID/BOTTOM
//       DDR STAT0
//       DDR STAT1
//       SDA
// The order of the PLACEMENT_VEC is determined by the above tree of
// merged_logging_bus: sda ocl bar1 pcim pcis
parameter int LOGE_PER_AXI = 5;
parameter int AWSF1_NUM_INTERFACES = 5;
parameter int AWSF1_PLACEMENT_VEC[AWSF1_NUM_INTERFACES-1:0] = '{
  5, // sda
  3, // ocl
  0, // bar1
  1, // pcim
  4  // pcis
};
// The alignment of packets
`ifndef OVERRIDE_PACKET_ALIGNMENT
parameter int PACKET_ALIGNMENT = 8;
`else
parameter int PACKET_ALIGNMENT = `OVERRIDE_PACKET_ALIGNMENT;
`endif
parameter logic [63:0] PACKET_ALIGNMENT_SHIFT = $clog2(PACKET_ALIGNMENT);
parameter logic [63:0] PACKET_ALIGNMENT_MASK = 64'(PACKET_ALIGNMENT) - 1;
// GET_ALIGNED_SIZE is to align constant parameters
`define GET_ALIGNED_SIZE(size) (((size - 1) / PACKET_ALIGNMENT + 1) * PACKET_ALIGNMENT)
// GET_ALIGNED_SIZE_W is to align known-width variables
// It uses more efficient bit ops.
`define GET_ALIGNED_SIZE_W(width, size)                                        \
  (((size) + width'(PACKET_ALIGNMENT) - 1) & (~(width'(PACKET_ALIGNMENT) - 1)))
`define GET_FORCE_ALIGNED_SIZE(size) (size & ~PACKET_ALIGNMENT_MASK)
`define GET_FORCE_ALIGNED_FRAME(size) (size >> PACKET_ALIGNMENT_SHIFT)
`define IS_ALIGNED_SIZE(size) ((size & PACKET_ALIGNMENT_MASK) == 0)
`endif // CL_FPGARR_DEFS
