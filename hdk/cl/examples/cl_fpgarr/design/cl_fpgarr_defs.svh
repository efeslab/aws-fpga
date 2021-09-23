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

// macro utility to connect verilog wire signals to systemverilog interfaces
// b for bus, m for master, s for slave
// bus signals are accessed via `b.Xvalid`
// wire signals are accessed via name concatenation of m, s, pfx and field names
// pfx is prefix
// TODO: seperate rr axi bus definition and remove wid
// TODO: pcis Xid is just 6bit
`define AXI_MSTR_WIRE2BUS(b, m, s, pfx)                                        \
  axi_bus_t b();                                                               \
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
  axi_bus_t b();                                                               \
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
  axi_lite_bus_t b();                                                          \
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
  axi_lite_bus_t b();                                                          \
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
`endif // CL_FPGARR_DEFS
