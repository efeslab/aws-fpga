`ifndef CL_FPGARR_PKG
`define CL_FPGARR_PKG
`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"
// TODO: use packaging to isolate rr's definition of axi_bus from cl's
// definition (if there is any)
   interface axi_bus_t;
      logic[15:0] awid;
      logic[63:0] awaddr;
      logic[7:0] awlen;
      logic [2:0] awsize;
      logic awvalid;
      logic awready;
   
      logic[15:0] wid;
      logic[511:0] wdata;
      logic[63:0] wstrb;
      logic wlast;
      logic wvalid;
      logic wready;
         
      logic[15:0] bid;
      logic[1:0] bresp;
      logic bvalid;
      logic bready;
         
      logic[15:0] arid;
      logic[63:0] araddr;
      logic[7:0] arlen;
      logic [2:0] arsize;
      logic arvalid;
      logic arready;
         
      logic[15:0] rid;
      logic[511:0] rdata;
      logic[1:0] rresp;
      logic rlast;
      logic rvalid;
      logic rready;

      modport master (input awid, awaddr, awlen, awsize, awvalid, output awready,
                      input wid, wdata, wstrb, wlast, wvalid, output wready,
                      output bid, bresp, bvalid, input bready,
                      input arid, araddr, arlen, arsize, arvalid, output arready,
                      output rid, rdata, rresp, rlast, rvalid, input rready);

      modport slave  (output awid, awaddr, awlen, awsize, awvalid, input awready,
                     output wid, wdata, wstrb, wlast, wvalid, input wready,
                     input bid, bresp, bvalid, output bready,
                     output arid, araddr, arlen, arsize, arvalid, input arready,
                     input rid, rdata, rresp, rlast, rvalid, output rready);
   endinterface

   interface axi_lite_bus_t;
      // Write Address
      logic [31:0] awaddr;
      logic awvalid;
      logic awready;
      // Write Data
      logic [31:0] wdata;
      logic [3:0] wstrb;
      logic wvalid;
      logic wready;
      // Write Response
      logic [1:0] bresp;
      logic bvalid;
      logic bready;
      // Read Address
      logic [31:0] araddr;
      logic arvalid;
      logic arready;
      // Read Response
      logic [31:0] rdata;
      logic [1:0] rresp;
      logic rvalid;
      logic rready;

      modport master (input awaddr, awvalid, output awready,
                         input wdata, wstrb, wvalid, output wready,
                         output bresp, bvalid, input bready,
                         input araddr, arvalid, output arready,
                         output rdata, rresp, rvalid, input rready);

      modport slave  (output awaddr, awvalid, input awready,
                         output wdata, wstrb, wvalid, input wready,
                         input bresp, bvalid, output bready,
                         output araddr, arvalid, input arready,
                         input rdata, rresp, rvalid, output rready);
   endinterface

   // rr_logging_bus_t holds the unpacked logb_data
   // You should refer to the parameter array CHANNEL_WIDTHS for how to parse
   // the logb_data
   interface rr_logging_bus_t #(
      // how many channel you want to log transaction starts
      // This is for logging what transaction to replay
      parameter int LOGB_CHANNEL_CNT,
      parameter bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0] CHANNEL_WIDTHS,
      // how many channel you want to log transaction ends
      // This is for logging the ordering/happen-before across transactions
      parameter int LOGE_CHANNEL_CNT
   );
   function automatic int GET_FULL_WIDTH;
      GET_FULL_WIDTH = 0;
      for (int i=0; i < LOGB_CHANNEL_CNT; ++i)
         GET_FULL_WIDTH += CHANNEL_WIDTHS[i];
   endfunction
   parameter FULL_WIDTH = GET_FULL_WIDTH();
   logic logb_valid [LOGB_CHANNEL_CNT-1:0];
   logic [FULL_WIDTH-1:0] logb_data;
   logic loge_valid [LOGE_CHANNEL_CNT-1:0];
   // this is shared between logb and loge
   // i.e. ready == logb_ready == loge_ready
   logic ready;
   modport P (output logb_valid, output logb_data,
              output loge_valid, input ready);
   modport C (input logb_valid, input logb_data,
              input loge_valid, output ready);
   endinterface

   interface rr_packed_logging_bus_t #(
      parameter int LOGB_CHANNEL_CNT,
      parameter int LOGE_CHANNEL_CNT,
      parameter int FULL_WIDTH
   );
   // here, use $clog2(FULL_WIDTH+1) because if FULL_WIDTH == 32, then
   // $clog2(32) == 5, but 5 bits cannot represent the integer 32.
   parameter OFFSET_WIDTH = $clog2(FULL_WIDTH+1);

   typedef struct packed {
      // to aggregate whether at least one of the packed logb has valid data
      // This is also the `valid` indicator for the logb_data and logb_data_len
      logic any_valid;
      // Note that data and len are only meaningful if any_valid is true
      // data is the packed version of all valid data of each logb channel
      logic [FULL_WIDTH-1:0] data;
      // len is the total length of the valid data. There are at most
      // FULL_WIDTH bits of valid data (every channel has valid data)
      logic [OFFSET_WIDTH-1:0] len;
   } packed_data_t;

   logic [LOGB_CHANNEL_CNT-1:0] logb_valid;
   packed_data_t plogb; // packed logb
   logic [LOGE_CHANNEL_CNT-1:0] loge_valid;
   logic ready;
   modport P (output logb_valid, plogb, loge_valid,
              input ready);
   modport C (input logb_valid, plogb, loge_valid,
              output ready);
   endinterface

   // This is supposed to be the interface between mjc and I
   interface rr_writeback_bus_t #(
      parameter int FULL_WIDTH
   );
   parameter OFFSET_WIDTH = $clog2(FULL_WIDTH+1);
   logic valid;
   // LSB to MSB: logb_valid, loge_valid, packed_logb_data
   logic [FULL_WIDTH-1:0] data;
   logic [OFFSET_WIDTH-1:0] len;
   logic ready;
   endinterface
`endif
