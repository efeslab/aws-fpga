`ifndef FORMAL_PROPERTIES
`define FORMAL_PROPERTIES
// reset clears VALID
property RESET_CLEARS_VALID(clk, rstn, valid);
  @(posedge clk) !rstn |=> !valid;
endproperty

// Following any stall (VALID && !READY), valid must remain and data must be
// stable
property HELD_VALID_DATA(clk, rstn, valid, ready, data);
  @(posedge clk) disable iff (!rstn)
  (valid && !ready) |=> (valid && $stable(data));
endproperty
`endif
