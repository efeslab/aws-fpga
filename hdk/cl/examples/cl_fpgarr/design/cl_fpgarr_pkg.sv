`ifndef CL_FPGARR_PKG
`define CL_FPGARR_PKG
`include "cl_fpgarr_defs.svh"
`include "cl_fpgarr_types.svh"
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
   function automatic int GET_OFFSET (int idx);
      GET_OFFSET = 0;
      for (int i=0; i < idx; i=i+1)
         GET_OFFSET += CHANNEL_WIDTHS[i];
   endfunction
   parameter OFFSET_WIDTH = $clog2(GET_FULL_WIDTH());
   localparam FULL_WIDTH = GET_FULL_WIDTH();
   logic logb_valid [LOGB_CHANNEL_CNT-1:0];
   logic [FULL_WIDTH-1:0] logb_data;
   logic loge_valid [LOGE_CHANNEL_CNT-1:0];
   // this is shared between logb and loge
   // i.e. ready == logb_ready == loge_ready
   logic ready;
   modport P (output logb_valid, output logb_data,
              output loge_valid, input ready, import GET_OFFSET);
   modport C (input logb_valid, input logb_data,
              input loge_valid, output ready);
   endinterface

`endif
