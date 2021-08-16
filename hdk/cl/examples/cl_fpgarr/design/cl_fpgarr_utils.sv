module axi_to_axil_master(
   axi_bus_t.master axi,
   axi_lite_bus_t.slave axil);
   // AW Channel
   assign axil.awaddr = axi.awaddr[31:0];
   assign axil.awvalid = axi.awvalid;
   assign axi.awready = axil.awready;
   // W  Channel
   assign axil.wdata = axi.wdata[31:0];
   assign axil.wstrb = axi.wstrb[3:0];
   assign axil.wvalid = axi.wvalid;
   assign axi.wready = axil.wready;
   // B  Channel
   assign axi.bresp = axil.bresp;
   assign axi.bvalid = axil.bvalid;
   assign axil.bready = axi.bready;
   // AR Channel
   assign axil.araddr = axi.araddr[31:0];
   assign axil.arvalid = axi.arvalid;
   assign axi.arready = axil.arready;
   // R  Channel
   assign axi.rdata[31:0] = axil.rdata;
   assign axi.rresp = axil.rresp;
   assign axi.rvalid = axil.rvalid;
   assign axil.rready = axi.rready;
endmodule


////////////////////////////////////////////////////////////////////////////////
// reduction_and is to establish fake depenencies to prevent synthesizer from
// optimizing out circuits under test. This was useful when I wanted to
// estimate the timing/resource usage of unfinished circuits.
////////////////////////////////////////////////////////////////////////////////
module reduction_and #(
   parameter IN_WIDTH,
   parameter OUT_WIDTH) (
   input logic [IN_WIDTH-1:0] in,
   output logic [OUT_WIDTH-1:0] out);
   localparam REMAIN = IN_WIDTH % OUT_WIDTH;
   integer i;
   always_comb begin
      out = {OUT_WIDTH{1'b0}};
      for (i=OUT_WIDTH; i < IN_WIDTH; i+=OUT_WIDTH) begin
         out = out & in[i-1 -: OUT_WIDTH];
      end
      if (REMAIN > 0)
         out = out & {{OUT_WIDTH-REMAIN{1'b0}}, in[IN_WIDTH-REMAIN +: REMAIN]};
   end
endmodule

module channel_siderec #(
   parameter DEPTH,
   parameter WIDTH) (
   input  logic clk,
   input  logic sync_rst_n,
   input  logic [WIDTH-1:0] din,
   input  logic sh_valid,
   input  logic cl_ready,
   input  logic bubble_en,
   // fifo output
   output logic ispkt_out,
   output logic busy_out,
   output logic [WIDTH-1:0] dout,
   // fifo output handshake
   output logic rec_valid,
   input  logic rec_ready,
   // additional backpressure (fifo is full) to input
   output logic sh_ready,
   // output for bubble
   output logic new_packet
);

logic busy;
logic past_busy;
assign busy = sh_valid && !sh_ready;
always_ff@(posedge clk)
   if (!sync_rst_n)
      past_busy <= 0;
   else
      past_busy <= busy;
assign new_packet = !past_busy && sh_valid;

// The fifo to buffer recorded packets/transactions in this channel.
// Fifos on all channels are synchrohized.
// The content of the fifo buffer is
//      {whether this is a valid packet,
//       whether the current channel is busy when bubble is needed,
//       WIDTH bits packet content}
//
// When other fifos record a packet but this fifo does not have a new packet to
// record in this cycle, this fifo should also record whether this channel is
// busy for partial event ordering used during replay.
// Note that if the current channel is busy, the packets recorded by other
// fifos in this cycle can be replayed parallelly. Otherwise, packets
// recorded by other fifos should wait this channel to finish the previous
// packets.
// FIXME at this moment, I think the past_busy (i.e. one cycle before the
// bubble) should be recorded into the fifo, because the fact that the
// transaction is complete (valid && ready, or not-busy) will only be observed
// at next cycle (AXI spec forbid combination logic between input and output,
// so new packets sent the same cycle of completion is considered concurrent).
logic full;
flop_fifo #(.DEPTH(DEPTH), .WIDTH(WIDTH+2)) REC_FIFO (
   .clk(clk),
   .rst_n(sync_rst_n),
   .sync_rst_n(1'b1),
   .cfg_watermark(DEPTH),
   .push(new_packet || bubble_en),
   .push_data({new_packet, past_busy, din}),
   .pop(rec_valid && rec_ready),
   .pop_data({ispkt_out, busy_out, dout}),
   .half_full(),
   .watermark(full),
   .data_valid(rec_valid)
);
assign sh_ready = cl_ready && !full;
endmodule
