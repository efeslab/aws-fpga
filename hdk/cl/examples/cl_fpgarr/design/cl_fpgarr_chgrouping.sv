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
   if (inA.LOGB_DATA_WIDTH + inB.LOGB_DATA_WIDTH != out.LOGB_DATA_WIDTH)
      $error("LOGB_DATA_WIDTH mismatches: inA %d, inB %d, out %d\n",
         inA.LOGB_DATA_WIDTH, inB.LOGB_DATA_WIDTH, out.LOGB_DATA_WIDTH);
endgenerate
initial begin
   assert(check_CHANNEL_WIDTHS());
end
// end of parameter check
assign inA.logb_almful_hi = out.logb_almful_hi;
assign inB.logb_almful_hi = out.logb_almful_hi;
assign inA.logb_almful_lo = out.logb_almful_lo;
assign inB.logb_almful_lo = out.logb_almful_lo;
assign out.logb_valid[0 +: inA.LOGB_CHANNEL_CNT] = inA.logb_valid;
assign out.logb_valid[inA.LOGB_CHANNEL_CNT +: inB.LOGB_CHANNEL_CNT] = inB.logb_valid;
assign out.logb_data[0 +: inA.LOGB_DATA_WIDTH] = inA.logb_data;
assign out.logb_data[inA.LOGB_DATA_WIDTH +: inB.LOGB_DATA_WIDTH] = inB.logb_data;
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
// for axi-valid replay
localparam LOGB_LEFT_CNT = outA.LOGB_CHANNEL_CNT;
localparam LOGB_RIGHT_CNT = outB.LOGB_CHANNEL_CNT;
localparam bit [LOGB_CHANNEL_CNT-1:0] [RR_CHANNEL_WIDTH_BITS-1:0]
  CHANNEL_WIDTHS = in.CHANNEL_WIDTHS;
`DEF_SUM_WIDTH(GET_LEFT_WIDTH, CHANNEL_WIDTHS, 0, LOGB_LEFT_CNT)
`DEF_SUM_WIDTH(GET_RIGHT_WIDTH, CHANNEL_WIDTHS, LOGB_LEFT_CNT, LOGB_CHANNEL_CNT)
localparam LEFT_WIDTH = GET_LEFT_WIDTH();
localparam RIGHT_WIDTH = GET_RIGHT_WIDTH();
// for axi-ready replay
localparam LEFT_NUM_INTF = outA.NUM_AXI_INTF;
localparam RIGHT_NUM_INTF = outB.NUM_AXI_INTF;

//// parameter check
if (LOGB_LEFT_CNT + LOGB_RIGHT_CNT != LOGB_CHANNEL_CNT)
  $error("LOGB_CHANNEL_CNT mismatch: LOGB_CHANNEL_CNT %d, outA %d, outB %d\n",
    LOGB_CHANNEL_CNT, LOGB_LEFT_CNT, LOGB_RIGHT_CNT);
if (LEFT_WIDTH != outA.LOGB_DATA_WIDTH)
  $error("LEFT_WIDTH mismatch: LEFT_WIDTH %d, outA %d\n",
    LEFT_WIDTH, outA.LOGB_DATA_WIDTH);
if (RIGHT_WIDTH != outB.LOGB_DATA_WIDTH)
  $error("RIGHT_WIDTH mismatch: RIGHT_WIDTH %d, outB %d\n",
    RIGHT_WIDTH, outB.LOGB_DATA_WIDTH);
if ((LOGE_CHANNEL_CNT != outA.LOGE_CHANNEL_CNT) ||
    (LOGE_CHANNEL_CNT != outB.LOGE_CHANNEL_CNT))
  $error("LOGE_CHANNEL_CNT mismatch: in %d, outA %d, outB %d\n",
    LOGE_CHANNEL_CNT, outA.LOGE_CHANNEL_CNT, outB.LOGE_CHANNEL_CNT);
if (LEFT_NUM_INTF + RIGHT_NUM_INTF != in.NUM_AXI_INTF)
  $error("NUM_AXI_INTF mismatches: left %d, right %d, in %d",
    LEFT_NUM_INTF, RIGHT_NUM_INTF, in.NUM_AXI_INTF);

genvar i;
generate
  // for axi-valid replay
  for (i=0; i < LOGB_LEFT_CNT; i=i+1) begin
    assign in.almful[i] = outA.almful[i];
    assign outA.valid[i] = in.valid[i];
    assign outA.logb_valid[i] = in.logb_valid[i];
    assign outA.loge_valid[i] = in.loge_valid[i];
  end
  assign outA.logb_data = in.logb_data[0 +: LEFT_WIDTH];
  for (i=0; i < LOGB_RIGHT_CNT; i=i+1) begin
    localparam IDX = LOGB_LEFT_CNT + i;
    assign in.almful[IDX] = outB.almful[i];
    assign outB.valid[i] = in.valid[IDX];
    assign outB.logb_valid[i] = in.logb_valid[IDX];
    assign outB.loge_valid[i] = in.loge_valid[IDX];
  end
  assign outB.logb_data = in.logb_data[LEFT_WIDTH +: RIGHT_WIDTH];
  // for axi-ready replay
  for (i=0; i < LEFT_NUM_INTF; i=i+1) begin
    assign in.rdyrply_almful[i] = outA.rdyrply_almful[i];
    assign outA.rdyrply_valid[i] = in.rdyrply_valid[i];
    assign outA.rdyrply_loge_valid[i] = in.rdyrply_loge_valid[i];
  end
  for (i=0; i < RIGHT_NUM_INTF; i=i+1) begin
    localparam IDX = LEFT_NUM_INTF + i;
    assign in.rdyrply_almful[IDX] = outB.rdyrply_almful[i];
    assign outB.rdyrply_valid[i] = in.rdyrply_valid[IDX];
    assign outB.rdyrply_loge_valid[i] = in.rdyrply_loge_valid[IDX];
  end
endgenerate

endmodule

// drop any logging content
module rr_logging_bus_blackhole (
  rr_logging_bus_t.C in
);
  assign in.logb_almful_hi = 0;
  assign in.logb_almful_lo = 0;
endmodule

// pass through (aka. rename) a logging_bus
module rr_logging_bus_pt (
  rr_logging_bus_t.C in,
  rr_logging_bus_t.P out
);
  // parameter check
  if (in.LOGB_CHANNEL_CNT != out.LOGB_CHANNEL_CNT)
    $error("LOGB_CHANNEL_CNT mismatches: in %d, out %d\n",
      in.LOGB_CHANNEL_CNT, out.LOGB_CHANNEL_CNT
    );
  if (in.LOGE_CHANNEL_CNT != out.LOGE_CHANNEL_CNT)
    $error("LOGE_CHANNEL_CNT mismatches: in %d, out %d\n",
      in.LOGE_CHANNEL_CNT, out.LOGE_CHANNEL_CNT
    );
  if (in.CHANNEL_WIDTHS != out.CHANNEL_WIDTHS)
    $error("CHANNEL_WIDTHS mismatches: in %d, out %d\n",
      in.CHANNEL_WIDTHS, out.CHANNEL_WIDTHS
    );
  if (in.LOGB_CHANNEL_NAMES != out.LOGB_CHANNEL_NAMES)
    $error("LOGB_CHANNEL_NAMES mismatches");
  if (in.LOGE_CHANNEL_NAMES != out.LOGE_CHANNEL_NAMES)
    $error("LOGE_CHANNEL_NAMES mismatches");
  for (genvar i = 0; i < in.LOGB_CHANNEL_CNT; i=i+1) begin: logb
    assign out.logb_valid[i] = in.logb_valid[i];
  end
  for (genvar i = 0; i < in.LOGE_CHANNEL_CNT; i=i+1) begin: loge
    assign out.loge_valid[i] = in.loge_valid[i];
  end
  assign out.logb_data = in.logb_data;
  assign in.logb_almful_hi = out.logb_almful_hi;
  assign in.logb_almful_lo = out.logb_almful_lo;
endmodule

// drive fake replay data out of nowhere
module rr_replay_bus_whitehole (
  rr_replay_bus_t.P out
);
  for (genvar i = 0; i < out.LOGB_CHANNEL_CNT; i=i+1) begin: logb
    assign out.valid[i] = 0;
    assign out.logb_valid[i] = 0;
    assign out.loge_valid[i] = 0;
  end
  for (genvar i = 0; i < out.NUM_AXI_INTF; i=i+1) begin: axi
    assign out.rdyrply_valid[i] = 0;
    assign out.rdyrply_loge_valid[i] = 0;
  end
  assign out.logb_data = 0;
endmodule

// pass through (aka. rename) a replay_bus
module rr_replay_bus_pt (
  rr_replay_bus_t.C in,
  rr_replay_bus_t.P out
);
  // parameter check
  if (in.LOGB_CHANNEL_CNT != out.LOGB_CHANNEL_CNT)
    $error("LOGB_CHANNEL_CNT mismatches: in %d, out %d\n",
      in.LOGB_CHANNEL_CNT, out.LOGB_CHANNEL_CNT
    );
  if (in.LOGE_CHANNEL_CNT != out.LOGE_CHANNEL_CNT)
    $error("LOGE_CHANNEL_CNT mismatches: in %d, out %d\n",
      in.LOGE_CHANNEL_CNT, out.LOGE_CHANNEL_CNT
    );
  if (in.CHANNEL_WIDTHS != out.CHANNEL_WIDTHS)
    $error("CHANNEL_WIDTHS mismatches");
  if (in.NUM_AXI_INTF != out.NUM_AXI_INTF)
    $error("NUM_AXI_INTF mismatches: in %d, out %d\n",
      in.NUM_AXI_INTF, out.NUM_AXI_INTF
    );
  for (genvar i = 0; i < in.LOGB_CHANNEL_CNT; i=i+1) begin: logb
    assign out.valid[i] = in.valid[i];
    assign out.logb_valid[i] = in.logb_valid[i];
    assign out.loge_valid[i] = in.loge_valid[i];
  end
  for (genvar i = 0; i < in.NUM_AXI_INTF; i=i+1) begin: axi
    assign out.rdyrply_valid[i] = in.rdyrply_valid[i];
    assign out.rdyrply_loge_valid[i] = in.rdyrply_loge_valid[i];
  end
  assign out.logb_data = in.logb_data;
  assign in.almful = out.almful;
  assign in.rdyrply_almful = out.rdyrply_almful;
endmodule
