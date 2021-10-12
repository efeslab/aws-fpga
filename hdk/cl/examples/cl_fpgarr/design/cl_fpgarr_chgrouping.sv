// Summary:
// rr_logging_bus_group2: group unpacked logging data
// rr_replay_bus_ungroup2: ungroup unpacked replay data

module rr_logging_bus_group2 (
   rr_logging_bus_t.C inA,
   rr_logging_bus_t.C inB,
   rr_logging_bus_t.P out
);
// From here localparams for the out logging bus
localparam LOGB_CHANNEL_CNT = out.LOGB_CHANNEL_CNT;
localparam LOGE_CHANNEL_CNT = out.LOGE_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
  CHANNEL_WIDTHS = out.CHANNEL_WIDTHS;
function automatic bit
   check_CHANNEL_WIDTHS();
   int j=0;
      for (int i=0; i < inA.LOGB_CHANNEL_CNT; i=i+1) begin
         bit [RR_CHANNEL_WIDTH_BITS-1:0] out_width = out.CHANNEL_WIDTHS[j];
         bit [RR_CHANNEL_WIDTH_BITS-1:0] in_width = inA.CHANNEL_WIDTHS[i];
         if (out_width != in_width) begin
            $error("CHANNEL_WIDTHS mismatch out@%d(%d) != inA[%d](%d)", j,
               out_width, i, in_width);
            return 0;
         end
         j = j + 1;
      end
      for (int i=0; i < inB.LOGB_CHANNEL_CNT; i=i+1) begin
         bit [RR_CHANNEL_WIDTH_BITS-1:0] out_width = out.CHANNEL_WIDTHS[j];
         bit [RR_CHANNEL_WIDTH_BITS-1:0] in_width = inB.CHANNEL_WIDTHS[i];
         if (out_width != in_width) begin
            $error("CHANNEL_WIDTHS mismatch out@%d(%d) != inB[%d](%d)", j,
               out_width, i, in_width);
            return 0;
         end
         j = j + 1;
      end
   return 1;
endfunction
// parameter check
generate
   if (inA.LOGB_CHANNEL_CNT + inB.LOGB_CHANNEL_CNT != LOGB_CHANNEL_CNT) 
      $error("LOGB mismatches: inA %d, inB %d, out %d\n",
         inA.LOGB_CHANNEL_CNT, inB.LOGB_CHANNEL_CNT, LOGB_CHANNEL_CNT
      );
   if (inA.LOGE_CHANNEL_CNT + inB.LOGE_CHANNEL_CNT != LOGE_CHANNEL_CNT) 
      $error("LOGE mismatches: inA %d, inB %d, out %d\n",
         inA.LOGE_CHANNEL_CNT, inB.LOGE_CHANNEL_CNT, LOGE_CHANNEL_CNT
      );
   if (inA.FULL_WIDTH + inB.FULL_WIDTH != out.FULL_WIDTH)
      $error("FULL_WIDTH mismatches: inA %d, inB %d, out %d\n",
         inA.FULL_WIDTH, inB.FULL_WIDTH, out.FULL_WIDTH);
endgenerate
initial begin
   assert(check_CHANNEL_WIDTHS());
end
// end of parameter check
assign inA.ready = out.ready;
assign inB.ready = out.ready;
assign out.logb_valid[0 +: inA.LOGB_CHANNEL_CNT] = inA.logb_valid;
assign out.logb_valid[inA.LOGB_CHANNEL_CNT +: inB.LOGB_CHANNEL_CNT] = inB.logb_valid;
assign out.logb_data[0 +: inA.FULL_WIDTH] = inA.logb_data;
assign out.logb_data[inA.FULL_WIDTH +: inB.FULL_WIDTH] = inB.logb_data;
assign out.loge_valid[0 +: inA.LOGE_CHANNEL_CNT] = inA.loge_valid;
assign out.loge_valid[inA.LOGE_CHANNEL_CNT +: inB.LOGE_CHANNEL_CNT] = inB.loge_valid;
endmodule

module rr_replay_bus_ungroup2 (
  rr_replay_bus_t.C in,
  rr_replay_bus_t.P outA,
  rr_replay_bus_t.P outB
);
localparam LOGB_CHANNEL_CNT = in.LOGB_CHANNEL_CNT;
localparam LOGE_CHANNEL_CNT = in.LOGE_CHANNEL_CNT;
localparam LOGB_LEFT_CNT = outA.LOGB_CHANNEL_CNT;
localparam LOGB_RIGHT_CNT = outB.LOGB_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
  CHANNEL_WIDTHS = in.CHANNEL_WIDTHS;
`DEF_SUM_WIDTH(GET_LEFT_WIDTH, CHANNEL_WIDTHS, 0, LOGB_LEFT_CNT)
`DEF_SUM_WIDTH(GET_RIGHT_WIDTH, CHANNEL_WIDTHS, LOGB_LEFT_CNT, LOGB_CHANNEL_CNT)
localparam LEFT_WIDTH = GET_LEFT_WIDTH();
localparam RIGHT_WIDTH = GET_RIGHT_WIDTH();

// parameter check
generate
  if (LOGB_LEFT_CNT + LOGB_RIGHT_CNT != LOGB_CHANNEL_CNT)
    $error("LOGB_CHANNEL_CNT mismatch: LOGB_CHANNEL_CNT %d, outA %d, outB %d\n",
      LOGB_CHANNEL_CNT, LOGB_LEFT_CNT, LOGB_RIGHT_CNT);
  if (LEFT_WIDTH != outA.FULL_WIDTH)
    $error("LEFT_WIDTH mismatch: LEFT_WIDTH %d, outA %d\n",
      LEFT_WIDTH, outA.FULL_WIDTH);
  if (RIGHT_WIDTH != outB.FULL_WIDTH)
    $error("RIGHT_WIDTH mismatch: RIGHT_WIDTH %d, outB %d\n",
      RIGHT_WIDTH, outB.FULL_WIDTH);
  if ((LOGE_CHANNEL_CNT != outA.LOGE_CHANNEL_CNT) ||
      (LOGE_CHANNEL_CNT != outB.LOGE_CHANNEL_CNT))
    $error("LOGE_CHANNEL_CNT mismatch: in %d, outA %d, outB %d\n",
      LOGE_CHANNEL_CNT, outA.LOGE_CHANNEL_CNT, outB.LOGE_CHANNEL_CNT);
endgenerate

genvar i;
generate
  for (i=0; i < LOGB_LEFT_CNT; i=i+1) begin
    assign in.ready[i] = outA.ready[i];
    assign outA.logb_valid[i] = in.logb_valid[i];
    assign outA.loge_valid[i] = in.loge_valid[i];
  end
  assign outA.logb_data = in.logb_data[0 +: LEFT_WIDTH];
  for (i=0; i < LOGB_RIGHT_CNT; i=i+1) begin
    localparam IDX = LOGB_LEFT_CNT + i;
    assign in.ready[IDX] = outB.ready[i];
    assign outB.logb_valid[i] = in.logb_valid[IDX];
    assign outB.loge_valid[i] = in.loge_valid[IDX];
  end
  assign outB.logb_data = in.logb_data[LEFT_WIDTH +: RIGHT_WIDTH];
endgenerate

endmodule
