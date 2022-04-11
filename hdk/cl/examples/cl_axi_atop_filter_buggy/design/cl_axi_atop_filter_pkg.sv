// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.
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

   modport slave (output awid, awaddr, awlen, awsize, awvalid, input awready,
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

interface axis_bus_t #(
  parameter DATA_WIDTH,
  parameter USER_WIDTH,
  parameter KEEP_WIDTH = (DATA_WIDTH/8)
);
  logic [DATA_WIDTH-1:0] tdata;
  logic [KEEP_WIDTH-1:0] tkeep;
  logic tvalid;
  logic tready;
  logic tlast;
  logic [USER_WIDTH-1:0] tuser;

  modport master (input tdata, tkeep, tvalid, tlast, tuser, output tready);
  modport slave (output tdata, tkeep, tvalid, tlast, tuser, input tready);
endinterface

interface axi_bus_W_t;
    logic[5:0] awid;
    logic[63:0] awaddr;
    logic[7:0] awlen;
    logic [2:0] awsize;
    logic awvalid;
    logic awready;
 
    logic[511:0] wdata;
    logic[63:0] wstrb;
    logic wlast;
    logic wvalid;
    logic wready;
       
    logic[5:0] bid;
    logic[1:0] bresp;
    logic bvalid;
    logic bready;

    modport master (input awid, awaddr, awlen, awsize, awvalid, output awready,
                    input wdata, wstrb, wlast, wvalid, output wready,
                    output bid, bresp, bvalid, input bready);

    modport slave  (output awid, awaddr, awlen, awsize, awvalid, input awready,
                   output wdata, wstrb, wlast, wvalid, input wready,
                   input bid, bresp, bvalid, output bready);
endinterface

`ifdef NOTUSED
module axi_W_blackhole (
  input wire clk,
  input wire rstn,
  input logic awvalid,
  output logic awready,
  input logic wvalid,
  output logic wready,
  output logic bvalid,
  input logic bready
);
// state machine
//       aw_received &&
//       w_received
// IDLE -----------------> SEND_B
//      <-----------------
//        bvalid && bready
typedef enum {IDLE, SEND_B} state_t;
state_t state;
logic aw_received;
logic w_received;

// state
always_ff @(posedge clk)
  if (!rstn)
    state <= IDLE;
  else
    case (state)
      IDLE:
        state <= (aw_received && w_received) ? SEND_B : IDLE;
      SEND_B:
        state <= (bvalid && bready) ? IDLE : SEND_B;
    endcase
assign bvalid = (state == SEND_B);

always_ff @(posedge clk)
  if (!rstn) begin
    aw_received <= 0;
    w_received <= 0;
  end
  else
    case (state == IDLE)
      IDLE: begin
        aw_received <= aw_received || (awvalid && awready);
        w_received <= w_received || (wvalid && wready);
      end
      SEND_B: begin
        aw_received <= !(bvalid && bready);
        w_received <= !(bvalid && bready);
      end
    endcase
assign awready = !aw_received;
assign wready = !w_received;
endmodule
`endif
