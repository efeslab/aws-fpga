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

// TODO: it is surprising but jg proves >2x slower (and the slowdown is also
// unstable) when I encapsulate boolean
// expressions with an additional layer of property macros.
// For example:
// `EVENTUAL_RISE(clk, rstn, sig)`, which normally took 200~300s
//   would be much faster than
// `EVENTUAL_DROP(clk, rstn, !sig)`, which spent >1000s and not finished yet.
// However, if I expand the macro and write the double negation !(!sig) directly
// in the assertion statement, then it becomes fast again.
//
// The given data will eventually flip its value (for liveness)
property EVENTUAL_RISE(clk, rstn, logic data);
  @(posedge clk) disable iff (!rstn)
  (!data) |-> ##[1:$] (data);
endproperty
property EVENTUAL_DROP(clk, rstn, logic data);
  @(posedge clk) disable iff (!rstn)
  (data) |-> ##[1:$] (!data);
endproperty
`endif
