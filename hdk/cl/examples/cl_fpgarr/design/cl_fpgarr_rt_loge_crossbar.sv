// This module is for the crossbar connection across different AXI(L) interfaces
// during replay. The crossbar needs to consider SLR crossing and add proper
// delays between certain interfaces.
//
// PLACEMENT_VEC is parameter array which represents the physical location (SLR)
// of the corresponding interface on the FPGA.
// The numerical difference of this placement metrics is used as the number of
// pipeline stages to be inserted when propagating the runtime loge_valid across
// all interfaces.
// If the difference is zero (e.g. one interfaces is zero distance from itself),
// then the loge_valid will be directly connected to the target.
module rr_rt_loge_crossbar #(
  parameter int LOGE_PER_INTERFACE,
  parameter int NUM_INTERFACES,
  parameter int PLACEMENT_VEC [NUM_INTERFACES-1:0]
) (
  input wire clk,
  input wire rstn,
  input logic [LOGE_PER_INTERFACE-1:0] rt_loge_in [NUM_INTERFACES-1:0],
  output logic [NUM_INTERFACES-1:0] [LOGE_PER_INTERFACE-1:0]
    rt_loge_out [NUM_INTERFACES-1:0]
);

function automatic int ABS(int x, int y);
  if (x < y)
    ABS = y - x;
  else
    ABS = x - y;
endfunction

genvar s; // source interface
genvar t; // target interface
generate
  for (s=0; s < NUM_INTERFACES; s=s+1)
    for (t=0; t < NUM_INTERFACES; t=t+1) begin: crossbar
      localparam int DIST = ABS(PLACEMENT_VEC[s], PLACEMENT_VEC[t]);
      if (DIST == 0)
        assign rt_loge_out[t][s] = rt_loge_in[s];
      else
        lib_pipe #(.WIDTH(LOGE_PER_INTERFACE), .STAGES(DIST)) q (
          .clk(clk), .rst_n(rstn),
          .in_bus(rt_loge_in[s]),
          .out_bus(rt_loge_out[t][s]));
    end
endgenerate
endmodule
