module rr_packed2writeback_bus (
   input wire clk,
   input wire rstn,
   rr_packed_logging_bus_t in,
   rr_writeback_bus_t out
);

// parameter check
generate
   if (in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT + in.FULL_WIDTH
       != out.FULL_WIDTH)
    $error("Writeback FULL_WIDTH mismatch: logb W%d, loge W%d, packed_logb_data W%d, writeback W%d\n",
      in.LOGB_CHANNEL_CNT, in.LOGE_CHANNEL_CNT, in.FULL_WIDTH, out.FULL_WIDTH);
endgenerate

// loge_valid_output is the signal outputting to the writeback_bus
// loge_valid_output[i] shows whether one (and can only be one) transaction has
// finished on channel[i] between now (some logb_valid are true) and the last
// time some logb are valid.
// if logb_valid[i] && loge_valid[i], which only happen if the transaction
// really lasts for only one cycle (ready was asserted in advance)
logic [in.LOGE_CHANNEL_CNT-1:0] loge_valid_out;

assign out.valid = in.plogb.any_valid;
assign in.ready = out.ready;
assign out.len = out.valid?
   (in.plogb.len + out.OFFSET_WIDTH'(in.LOGB_CHANNEL_CNT + in.LOGE_CHANNEL_CNT))
   : 0;
// from LSB to MSB:
// logb_valid, loge_valid, packed_logb_data
assign out.data = {in.plogb.data, loge_valid_out, in.logb_valid};

// buf loge_valid if there is no valid logb to send
always @(posedge clk)
if (!rstn)
   loge_valid_out <= 0;
else
   for (int i=0; i < in.LOGE_CHANNEL_CNT; i=i+1)
      if (out.valid && in.loge_valid[i])
         loge_valid_out[i] <= 1;
      else if (out.valid && !in.loge_valid[i])
         loge_valid_out[i] <= 0;
      else if (!out.valid && in.loge_valid[i]) begin
         loge_valid_out[i] <= 1;
         no_loge_overwrite: assert(!loge_valid_out[i]);
      end
      else // !out.valid && !in.loge_valid[i]
         loge_valid_out[i] <= loge_valid_out[i];
endmodule
