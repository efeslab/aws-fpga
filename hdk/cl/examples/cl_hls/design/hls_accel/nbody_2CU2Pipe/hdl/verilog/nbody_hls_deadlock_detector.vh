
    wire reset;
    wire clock;
    assign reset = ap_rst_n;
    assign clock = ap_clk;
    wire [4:0] proc_0_data_FIFO_blk;
    wire [4:0] proc_0_data_PIPO_blk;
    wire [4:0] proc_0_start_FIFO_blk;
    wire [4:0] proc_0_TLF_FIFO_blk;
    wire [4:0] proc_0_input_sync_blk;
    wire [4:0] proc_0_output_sync_blk;
    wire [4:0] proc_dep_vld_vec_0;
    reg [4:0] proc_dep_vld_vec_0_reg;
    wire [4:0] in_chan_dep_vld_vec_0;
    wire [44:0] in_chan_dep_data_vec_0;
    wire [4:0] token_in_vec_0;
    wire [4:0] out_chan_dep_vld_vec_0;
    wire [8:0] out_chan_dep_data_0;
    wire [4:0] token_out_vec_0;
    wire dl_detect_out_0;
    wire dep_chan_vld_1_0;
    wire [8:0] dep_chan_data_1_0;
    wire token_1_0;
    wire dep_chan_vld_2_0;
    wire [8:0] dep_chan_data_2_0;
    wire token_2_0;
    wire dep_chan_vld_3_0;
    wire [8:0] dep_chan_data_3_0;
    wire token_3_0;
    wire dep_chan_vld_4_0;
    wire [8:0] dep_chan_data_4_0;
    wire token_4_0;
    wire dep_chan_vld_5_0;
    wire [8:0] dep_chan_data_5_0;
    wire token_5_0;
    wire [2:0] proc_1_data_FIFO_blk;
    wire [2:0] proc_1_data_PIPO_blk;
    wire [2:0] proc_1_start_FIFO_blk;
    wire [2:0] proc_1_TLF_FIFO_blk;
    wire [2:0] proc_1_input_sync_blk;
    wire [2:0] proc_1_output_sync_blk;
    wire [2:0] proc_dep_vld_vec_1;
    reg [2:0] proc_dep_vld_vec_1_reg;
    wire [2:0] in_chan_dep_vld_vec_1;
    wire [26:0] in_chan_dep_data_vec_1;
    wire [2:0] token_in_vec_1;
    wire [2:0] out_chan_dep_vld_vec_1;
    wire [8:0] out_chan_dep_data_1;
    wire [2:0] token_out_vec_1;
    wire dl_detect_out_1;
    wire dep_chan_vld_0_1;
    wire [8:0] dep_chan_data_0_1;
    wire token_0_1;
    wire dep_chan_vld_6_1;
    wire [8:0] dep_chan_data_6_1;
    wire token_6_1;
    wire dep_chan_vld_7_1;
    wire [8:0] dep_chan_data_7_1;
    wire token_7_1;
    wire [5:0] proc_2_data_FIFO_blk;
    wire [5:0] proc_2_data_PIPO_blk;
    wire [5:0] proc_2_start_FIFO_blk;
    wire [5:0] proc_2_TLF_FIFO_blk;
    wire [5:0] proc_2_input_sync_blk;
    wire [5:0] proc_2_output_sync_blk;
    wire [5:0] proc_dep_vld_vec_2;
    reg [5:0] proc_dep_vld_vec_2_reg;
    wire [5:0] in_chan_dep_vld_vec_2;
    wire [53:0] in_chan_dep_data_vec_2;
    wire [5:0] token_in_vec_2;
    wire [5:0] out_chan_dep_vld_vec_2;
    wire [8:0] out_chan_dep_data_2;
    wire [5:0] token_out_vec_2;
    wire dl_detect_out_2;
    wire dep_chan_vld_0_2;
    wire [8:0] dep_chan_data_0_2;
    wire token_0_2;
    wire dep_chan_vld_3_2;
    wire [8:0] dep_chan_data_3_2;
    wire token_3_2;
    wire dep_chan_vld_4_2;
    wire [8:0] dep_chan_data_4_2;
    wire token_4_2;
    wire dep_chan_vld_5_2;
    wire [8:0] dep_chan_data_5_2;
    wire token_5_2;
    wire dep_chan_vld_6_2;
    wire [8:0] dep_chan_data_6_2;
    wire token_6_2;
    wire dep_chan_vld_7_2;
    wire [8:0] dep_chan_data_7_2;
    wire token_7_2;
    wire [5:0] proc_3_data_FIFO_blk;
    wire [5:0] proc_3_data_PIPO_blk;
    wire [5:0] proc_3_start_FIFO_blk;
    wire [5:0] proc_3_TLF_FIFO_blk;
    wire [5:0] proc_3_input_sync_blk;
    wire [5:0] proc_3_output_sync_blk;
    wire [5:0] proc_dep_vld_vec_3;
    reg [5:0] proc_dep_vld_vec_3_reg;
    wire [5:0] in_chan_dep_vld_vec_3;
    wire [53:0] in_chan_dep_data_vec_3;
    wire [5:0] token_in_vec_3;
    wire [5:0] out_chan_dep_vld_vec_3;
    wire [8:0] out_chan_dep_data_3;
    wire [5:0] token_out_vec_3;
    wire dl_detect_out_3;
    wire dep_chan_vld_0_3;
    wire [8:0] dep_chan_data_0_3;
    wire token_0_3;
    wire dep_chan_vld_2_3;
    wire [8:0] dep_chan_data_2_3;
    wire token_2_3;
    wire dep_chan_vld_4_3;
    wire [8:0] dep_chan_data_4_3;
    wire token_4_3;
    wire dep_chan_vld_5_3;
    wire [8:0] dep_chan_data_5_3;
    wire token_5_3;
    wire dep_chan_vld_6_3;
    wire [8:0] dep_chan_data_6_3;
    wire token_6_3;
    wire dep_chan_vld_7_3;
    wire [8:0] dep_chan_data_7_3;
    wire token_7_3;
    wire [5:0] proc_4_data_FIFO_blk;
    wire [5:0] proc_4_data_PIPO_blk;
    wire [5:0] proc_4_start_FIFO_blk;
    wire [5:0] proc_4_TLF_FIFO_blk;
    wire [5:0] proc_4_input_sync_blk;
    wire [5:0] proc_4_output_sync_blk;
    wire [5:0] proc_dep_vld_vec_4;
    reg [5:0] proc_dep_vld_vec_4_reg;
    wire [5:0] in_chan_dep_vld_vec_4;
    wire [53:0] in_chan_dep_data_vec_4;
    wire [5:0] token_in_vec_4;
    wire [5:0] out_chan_dep_vld_vec_4;
    wire [8:0] out_chan_dep_data_4;
    wire [5:0] token_out_vec_4;
    wire dl_detect_out_4;
    wire dep_chan_vld_0_4;
    wire [8:0] dep_chan_data_0_4;
    wire token_0_4;
    wire dep_chan_vld_2_4;
    wire [8:0] dep_chan_data_2_4;
    wire token_2_4;
    wire dep_chan_vld_3_4;
    wire [8:0] dep_chan_data_3_4;
    wire token_3_4;
    wire dep_chan_vld_5_4;
    wire [8:0] dep_chan_data_5_4;
    wire token_5_4;
    wire dep_chan_vld_6_4;
    wire [8:0] dep_chan_data_6_4;
    wire token_6_4;
    wire dep_chan_vld_7_4;
    wire [8:0] dep_chan_data_7_4;
    wire token_7_4;
    wire [5:0] proc_5_data_FIFO_blk;
    wire [5:0] proc_5_data_PIPO_blk;
    wire [5:0] proc_5_start_FIFO_blk;
    wire [5:0] proc_5_TLF_FIFO_blk;
    wire [5:0] proc_5_input_sync_blk;
    wire [5:0] proc_5_output_sync_blk;
    wire [5:0] proc_dep_vld_vec_5;
    reg [5:0] proc_dep_vld_vec_5_reg;
    wire [5:0] in_chan_dep_vld_vec_5;
    wire [53:0] in_chan_dep_data_vec_5;
    wire [5:0] token_in_vec_5;
    wire [5:0] out_chan_dep_vld_vec_5;
    wire [8:0] out_chan_dep_data_5;
    wire [5:0] token_out_vec_5;
    wire dl_detect_out_5;
    wire dep_chan_vld_0_5;
    wire [8:0] dep_chan_data_0_5;
    wire token_0_5;
    wire dep_chan_vld_2_5;
    wire [8:0] dep_chan_data_2_5;
    wire token_2_5;
    wire dep_chan_vld_3_5;
    wire [8:0] dep_chan_data_3_5;
    wire token_3_5;
    wire dep_chan_vld_4_5;
    wire [8:0] dep_chan_data_4_5;
    wire token_4_5;
    wire dep_chan_vld_6_5;
    wire [8:0] dep_chan_data_6_5;
    wire token_6_5;
    wire dep_chan_vld_7_5;
    wire [8:0] dep_chan_data_7_5;
    wire token_7_5;
    wire [5:0] proc_6_data_FIFO_blk;
    wire [5:0] proc_6_data_PIPO_blk;
    wire [5:0] proc_6_start_FIFO_blk;
    wire [5:0] proc_6_TLF_FIFO_blk;
    wire [5:0] proc_6_input_sync_blk;
    wire [5:0] proc_6_output_sync_blk;
    wire [5:0] proc_dep_vld_vec_6;
    reg [5:0] proc_dep_vld_vec_6_reg;
    wire [5:0] in_chan_dep_vld_vec_6;
    wire [53:0] in_chan_dep_data_vec_6;
    wire [5:0] token_in_vec_6;
    wire [5:0] out_chan_dep_vld_vec_6;
    wire [8:0] out_chan_dep_data_6;
    wire [5:0] token_out_vec_6;
    wire dl_detect_out_6;
    wire dep_chan_vld_1_6;
    wire [8:0] dep_chan_data_1_6;
    wire token_1_6;
    wire dep_chan_vld_2_6;
    wire [8:0] dep_chan_data_2_6;
    wire token_2_6;
    wire dep_chan_vld_3_6;
    wire [8:0] dep_chan_data_3_6;
    wire token_3_6;
    wire dep_chan_vld_4_6;
    wire [8:0] dep_chan_data_4_6;
    wire token_4_6;
    wire dep_chan_vld_5_6;
    wire [8:0] dep_chan_data_5_6;
    wire token_5_6;
    wire dep_chan_vld_8_6;
    wire [8:0] dep_chan_data_8_6;
    wire token_8_6;
    wire [5:0] proc_7_data_FIFO_blk;
    wire [5:0] proc_7_data_PIPO_blk;
    wire [5:0] proc_7_start_FIFO_blk;
    wire [5:0] proc_7_TLF_FIFO_blk;
    wire [5:0] proc_7_input_sync_blk;
    wire [5:0] proc_7_output_sync_blk;
    wire [5:0] proc_dep_vld_vec_7;
    reg [5:0] proc_dep_vld_vec_7_reg;
    wire [5:0] in_chan_dep_vld_vec_7;
    wire [53:0] in_chan_dep_data_vec_7;
    wire [5:0] token_in_vec_7;
    wire [5:0] out_chan_dep_vld_vec_7;
    wire [8:0] out_chan_dep_data_7;
    wire [5:0] token_out_vec_7;
    wire dl_detect_out_7;
    wire dep_chan_vld_1_7;
    wire [8:0] dep_chan_data_1_7;
    wire token_1_7;
    wire dep_chan_vld_2_7;
    wire [8:0] dep_chan_data_2_7;
    wire token_2_7;
    wire dep_chan_vld_3_7;
    wire [8:0] dep_chan_data_3_7;
    wire token_3_7;
    wire dep_chan_vld_4_7;
    wire [8:0] dep_chan_data_4_7;
    wire token_4_7;
    wire dep_chan_vld_5_7;
    wire [8:0] dep_chan_data_5_7;
    wire token_5_7;
    wire dep_chan_vld_8_7;
    wire [8:0] dep_chan_data_8_7;
    wire token_8_7;
    wire [1:0] proc_8_data_FIFO_blk;
    wire [1:0] proc_8_data_PIPO_blk;
    wire [1:0] proc_8_start_FIFO_blk;
    wire [1:0] proc_8_TLF_FIFO_blk;
    wire [1:0] proc_8_input_sync_blk;
    wire [1:0] proc_8_output_sync_blk;
    wire [1:0] proc_dep_vld_vec_8;
    reg [1:0] proc_dep_vld_vec_8_reg;
    wire [1:0] in_chan_dep_vld_vec_8;
    wire [17:0] in_chan_dep_data_vec_8;
    wire [1:0] token_in_vec_8;
    wire [1:0] out_chan_dep_vld_vec_8;
    wire [8:0] out_chan_dep_data_8;
    wire [1:0] token_out_vec_8;
    wire dl_detect_out_8;
    wire dep_chan_vld_6_8;
    wire [8:0] dep_chan_data_6_8;
    wire token_6_8;
    wire dep_chan_vld_7_8;
    wire [8:0] dep_chan_data_7_8;
    wire token_7_8;
    wire [8:0] dl_in_vec;
    wire dl_detect_out;
    wire token_clear;
    reg [8:0] origin;

reg [15:0] trans_in_cnt_0;// for process grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0
always @(negedge reset or posedge clock) begin
    if (~reset) begin
         trans_in_cnt_0 <= 16'h0;
    end
    else if (grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.start_write == 1'b1) begin
        trans_in_cnt_0 <= trans_in_cnt_0 + 16'h1;
    end
    else begin
        trans_in_cnt_0 <= trans_in_cnt_0;
    end
end

reg [15:0] trans_out_cnt_0;// for process grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0
always @(negedge reset or posedge clock) begin
    if (~reset) begin
         trans_out_cnt_0 <= 16'h0;
    end
    else if (grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_done == 1'b1 && grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_continue == 1'b1) begin
        trans_out_cnt_0 <= trans_out_cnt_0 + 16'h1;
    end
    else begin
        trans_out_cnt_0 <= trans_out_cnt_0;
    end
end

reg [15:0] trans_in_cnt_1;// for process grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0
always @(negedge reset or posedge clock) begin
    if (~reset) begin
         trans_in_cnt_1 <= 16'h0;
    end
    else if (grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.start_write == 1'b1) begin
        trans_in_cnt_1 <= trans_in_cnt_1 + 16'h1;
    end
    else begin
        trans_in_cnt_1 <= trans_in_cnt_1;
    end
end

reg [15:0] trans_out_cnt_1;// for process grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0
always @(negedge reset or posedge clock) begin
    if (~reset) begin
         trans_out_cnt_1 <= 16'h0;
    end
    else if (grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_done == 1'b1 && grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_continue == 1'b1) begin
        trans_out_cnt_1 <= trans_out_cnt_1 + 16'h1;
    end
    else begin
        trans_out_cnt_1 <= trans_out_cnt_1;
    end
end

reg [15:0] trans_in_cnt_2;// for process grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0
always @(negedge reset or posedge clock) begin
    if (~reset) begin
         trans_in_cnt_2 <= 16'h0;
    end
    else if (grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.start_write == 1'b1) begin
        trans_in_cnt_2 <= trans_in_cnt_2 + 16'h1;
    end
    else begin
        trans_in_cnt_2 <= trans_in_cnt_2;
    end
end

reg [15:0] trans_out_cnt_2;// for process grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0
always @(negedge reset or posedge clock) begin
    if (~reset) begin
         trans_out_cnt_2 <= 16'h0;
    end
    else if (grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.ap_done == 1'b1 && grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.ap_continue == 1'b1) begin
        trans_out_cnt_2 <= trans_out_cnt_2 + 16'h1;
    end
    else begin
        trans_out_cnt_2 <= trans_out_cnt_2;
    end
end

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0
    nbody_hls_deadlock_detect_unit #(9, 0, 5, 5) nbody_hls_deadlock_detect_unit_0 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_0),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_0),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_0),
        .token_in_vec(token_in_vec_0),
        .dl_detect_in(dl_detect_out),
        .origin(origin[0]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_0),
        .out_chan_dep_data(out_chan_dep_data_0),
        .token_out_vec(token_out_vec_0),
        .dl_detect_out(dl_in_vec[0]));

    assign proc_0_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.x_val_out_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.y_val_out_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.z_val_out_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.EPS_out_blk_n);
    assign proc_0_data_PIPO_blk[0] = 1'b0;
    assign proc_0_start_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_entry38_U0_U.if_full_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_start & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.real_start & (trans_in_cnt_0 == trans_out_cnt_0) & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_entry38_U0_U.if_read);
    assign proc_0_TLF_FIFO_blk[0] = 1'b0;
    assign proc_0_input_sync_blk[0] = 1'b0;
    assign proc_0_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_0[0] = dl_detect_out ? proc_dep_vld_vec_0_reg[0] : (proc_0_data_FIFO_blk[0] | proc_0_data_PIPO_blk[0] | proc_0_start_FIFO_blk[0] | proc_0_TLF_FIFO_blk[0] | proc_0_input_sync_blk[0] | proc_0_output_sync_blk[0]);
    assign proc_0_data_FIFO_blk[1] = 1'b0;
    assign proc_0_data_PIPO_blk[1] = 1'b0;
    assign proc_0_start_FIFO_blk[1] = 1'b0;
    assign proc_0_TLF_FIFO_blk[1] = 1'b0;
    assign proc_0_input_sync_blk[1] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready);
    assign proc_0_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_0[1] = dl_detect_out ? proc_dep_vld_vec_0_reg[1] : (proc_0_data_FIFO_blk[1] | proc_0_data_PIPO_blk[1] | proc_0_start_FIFO_blk[1] | proc_0_TLF_FIFO_blk[1] | proc_0_input_sync_blk[1] | proc_0_output_sync_blk[1]);
    assign proc_0_data_FIFO_blk[2] = 1'b0;
    assign proc_0_data_PIPO_blk[2] = 1'b0;
    assign proc_0_start_FIFO_blk[2] = 1'b0;
    assign proc_0_TLF_FIFO_blk[2] = 1'b0;
    assign proc_0_input_sync_blk[2] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready);
    assign proc_0_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_0[2] = dl_detect_out ? proc_dep_vld_vec_0_reg[2] : (proc_0_data_FIFO_blk[2] | proc_0_data_PIPO_blk[2] | proc_0_start_FIFO_blk[2] | proc_0_TLF_FIFO_blk[2] | proc_0_input_sync_blk[2] | proc_0_output_sync_blk[2]);
    assign proc_0_data_FIFO_blk[3] = 1'b0;
    assign proc_0_data_PIPO_blk[3] = 1'b0;
    assign proc_0_start_FIFO_blk[3] = 1'b0;
    assign proc_0_TLF_FIFO_blk[3] = 1'b0;
    assign proc_0_input_sync_blk[3] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready);
    assign proc_0_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_0[3] = dl_detect_out ? proc_dep_vld_vec_0_reg[3] : (proc_0_data_FIFO_blk[3] | proc_0_data_PIPO_blk[3] | proc_0_start_FIFO_blk[3] | proc_0_TLF_FIFO_blk[3] | proc_0_input_sync_blk[3] | proc_0_output_sync_blk[3]);
    assign proc_0_data_FIFO_blk[4] = 1'b0;
    assign proc_0_data_PIPO_blk[4] = 1'b0;
    assign proc_0_start_FIFO_blk[4] = 1'b0;
    assign proc_0_TLF_FIFO_blk[4] = 1'b0;
    assign proc_0_input_sync_blk[4] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry3_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready);
    assign proc_0_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_0[4] = dl_detect_out ? proc_dep_vld_vec_0_reg[4] : (proc_0_data_FIFO_blk[4] | proc_0_data_PIPO_blk[4] | proc_0_start_FIFO_blk[4] | proc_0_TLF_FIFO_blk[4] | proc_0_input_sync_blk[4] | proc_0_output_sync_blk[4]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_0_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_0_reg <= proc_dep_vld_vec_0;
        end
    end
    assign in_chan_dep_vld_vec_0[0] = dep_chan_vld_1_0;
    assign in_chan_dep_data_vec_0[8 : 0] = dep_chan_data_1_0;
    assign token_in_vec_0[0] = token_1_0;
    assign in_chan_dep_vld_vec_0[1] = dep_chan_vld_2_0;
    assign in_chan_dep_data_vec_0[17 : 9] = dep_chan_data_2_0;
    assign token_in_vec_0[1] = token_2_0;
    assign in_chan_dep_vld_vec_0[2] = dep_chan_vld_3_0;
    assign in_chan_dep_data_vec_0[26 : 18] = dep_chan_data_3_0;
    assign token_in_vec_0[2] = token_3_0;
    assign in_chan_dep_vld_vec_0[3] = dep_chan_vld_4_0;
    assign in_chan_dep_data_vec_0[35 : 27] = dep_chan_data_4_0;
    assign token_in_vec_0[3] = token_4_0;
    assign in_chan_dep_vld_vec_0[4] = dep_chan_vld_5_0;
    assign in_chan_dep_data_vec_0[44 : 36] = dep_chan_data_5_0;
    assign token_in_vec_0[4] = token_5_0;
    assign dep_chan_vld_0_1 = out_chan_dep_vld_vec_0[0];
    assign dep_chan_data_0_1 = out_chan_dep_data_0;
    assign token_0_1 = token_out_vec_0[0];
    assign dep_chan_vld_0_2 = out_chan_dep_vld_vec_0[1];
    assign dep_chan_data_0_2 = out_chan_dep_data_0;
    assign token_0_2 = token_out_vec_0[1];
    assign dep_chan_vld_0_3 = out_chan_dep_vld_vec_0[2];
    assign dep_chan_data_0_3 = out_chan_dep_data_0;
    assign token_0_3 = token_out_vec_0[2];
    assign dep_chan_vld_0_4 = out_chan_dep_vld_vec_0[3];
    assign dep_chan_data_0_4 = out_chan_dep_data_0;
    assign token_0_4 = token_out_vec_0[3];
    assign dep_chan_vld_0_5 = out_chan_dep_vld_vec_0[4];
    assign dep_chan_data_0_5 = out_chan_dep_data_0;
    assign token_0_5 = token_out_vec_0[4];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0
    nbody_hls_deadlock_detect_unit #(9, 1, 3, 3) nbody_hls_deadlock_detect_unit_1 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_1),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_1),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_1),
        .token_in_vec(token_in_vec_1),
        .dl_detect_in(dl_detect_out),
        .origin(origin[1]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_1),
        .out_chan_dep_data(out_chan_dep_data_1),
        .token_out_vec(token_out_vec_1),
        .dl_detect_out(dl_in_vec[1]));

    assign proc_1_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.x_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.y_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.z_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.EPS_blk_n);
    assign proc_1_data_PIPO_blk[0] = 1'b0;
    assign proc_1_start_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_entry38_U0_U.if_empty_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_entry38_U0_U.if_write);
    assign proc_1_TLF_FIFO_blk[0] = 1'b0;
    assign proc_1_input_sync_blk[0] = 1'b0;
    assign proc_1_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_1[0] = dl_detect_out ? proc_dep_vld_vec_1_reg[0] : (proc_1_data_FIFO_blk[0] | proc_1_data_PIPO_blk[0] | proc_1_start_FIFO_blk[0] | proc_1_TLF_FIFO_blk[0] | proc_1_input_sync_blk[0] | proc_1_output_sync_blk[0]);
    assign proc_1_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.x_val_out_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.y_val_out_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.z_val_out_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.EPS_out_blk_n);
    assign proc_1_data_PIPO_blk[1] = 1'b0;
    assign proc_1_start_FIFO_blk[1] = 1'b0;
    assign proc_1_TLF_FIFO_blk[1] = 1'b0;
    assign proc_1_input_sync_blk[1] = 1'b0;
    assign proc_1_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_1[1] = dl_detect_out ? proc_dep_vld_vec_1_reg[1] : (proc_1_data_FIFO_blk[1] | proc_1_data_PIPO_blk[1] | proc_1_start_FIFO_blk[1] | proc_1_TLF_FIFO_blk[1] | proc_1_input_sync_blk[1] | proc_1_output_sync_blk[1]);
    assign proc_1_data_FIFO_blk[2] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.x_val_out1_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.y_val_out2_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.z_val_out3_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_entry38_U0.EPS_out4_blk_n);
    assign proc_1_data_PIPO_blk[2] = 1'b0;
    assign proc_1_start_FIFO_blk[2] = 1'b0;
    assign proc_1_TLF_FIFO_blk[2] = 1'b0;
    assign proc_1_input_sync_blk[2] = 1'b0;
    assign proc_1_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_1[2] = dl_detect_out ? proc_dep_vld_vec_1_reg[2] : (proc_1_data_FIFO_blk[2] | proc_1_data_PIPO_blk[2] | proc_1_start_FIFO_blk[2] | proc_1_TLF_FIFO_blk[2] | proc_1_input_sync_blk[2] | proc_1_output_sync_blk[2]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_1_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_1_reg <= proc_dep_vld_vec_1;
        end
    end
    assign in_chan_dep_vld_vec_1[0] = dep_chan_vld_0_1;
    assign in_chan_dep_data_vec_1[8 : 0] = dep_chan_data_0_1;
    assign token_in_vec_1[0] = token_0_1;
    assign in_chan_dep_vld_vec_1[1] = dep_chan_vld_6_1;
    assign in_chan_dep_data_vec_1[17 : 9] = dep_chan_data_6_1;
    assign token_in_vec_1[1] = token_6_1;
    assign in_chan_dep_vld_vec_1[2] = dep_chan_vld_7_1;
    assign in_chan_dep_data_vec_1[26 : 18] = dep_chan_data_7_1;
    assign token_in_vec_1[2] = token_7_1;
    assign dep_chan_vld_1_0 = out_chan_dep_vld_vec_1[0];
    assign dep_chan_data_1_0 = out_chan_dep_data_1;
    assign token_1_0 = token_out_vec_1[0];
    assign dep_chan_vld_1_6 = out_chan_dep_vld_vec_1[1];
    assign dep_chan_data_1_6 = out_chan_dep_data_1;
    assign token_1_6 = token_out_vec_1[1];
    assign dep_chan_vld_1_7 = out_chan_dep_vld_vec_1[2];
    assign dep_chan_data_1_7 = out_chan_dep_data_1;
    assign token_1_7 = token_out_vec_1[2];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0
    nbody_hls_deadlock_detect_unit #(9, 2, 6, 6) nbody_hls_deadlock_detect_unit_2 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_2),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_2),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_2),
        .token_in_vec(token_in_vec_2),
        .dl_detect_in(dl_detect_out),
        .origin(origin[2]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_2),
        .out_chan_dep_data(out_chan_dep_data_2),
        .token_out_vec(token_out_vec_2),
        .dl_detect_out(dl_in_vec[2]));

    assign proc_2_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.streamOut_V_V_blk_n);
    assign proc_2_data_PIPO_blk[0] = 1'b0;
    assign proc_2_start_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core27_U0_U.if_full_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_start & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.real_start & (trans_in_cnt_1 == trans_out_cnt_1) & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core27_U0_U.if_read);
    assign proc_2_TLF_FIFO_blk[0] = 1'b0;
    assign proc_2_input_sync_blk[0] = 1'b0;
    assign proc_2_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_2[0] = dl_detect_out ? proc_dep_vld_vec_2_reg[0] : (proc_2_data_FIFO_blk[0] | proc_2_data_PIPO_blk[0] | proc_2_start_FIFO_blk[0] | proc_2_TLF_FIFO_blk[0] | proc_2_input_sync_blk[0] | proc_2_output_sync_blk[0]);
    assign proc_2_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.streamOut_V_V1_blk_n);
    assign proc_2_data_PIPO_blk[1] = 1'b0;
    assign proc_2_start_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core28_U0_U.if_full_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_start & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.real_start & (trans_in_cnt_1 == trans_out_cnt_1) & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core28_U0_U.if_read);
    assign proc_2_TLF_FIFO_blk[1] = 1'b0;
    assign proc_2_input_sync_blk[1] = 1'b0;
    assign proc_2_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_2[1] = dl_detect_out ? proc_dep_vld_vec_2_reg[1] : (proc_2_data_FIFO_blk[1] | proc_2_data_PIPO_blk[1] | proc_2_start_FIFO_blk[1] | proc_2_TLF_FIFO_blk[1] | proc_2_input_sync_blk[1] | proc_2_output_sync_blk[1]);
    assign proc_2_data_FIFO_blk[2] = 1'b0;
    assign proc_2_data_PIPO_blk[2] = 1'b0;
    assign proc_2_start_FIFO_blk[2] = 1'b0;
    assign proc_2_TLF_FIFO_blk[2] = 1'b0;
    assign proc_2_input_sync_blk[2] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready);
    assign proc_2_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_2[2] = dl_detect_out ? proc_dep_vld_vec_2_reg[2] : (proc_2_data_FIFO_blk[2] | proc_2_data_PIPO_blk[2] | proc_2_start_FIFO_blk[2] | proc_2_TLF_FIFO_blk[2] | proc_2_input_sync_blk[2] | proc_2_output_sync_blk[2]);
    assign proc_2_data_FIFO_blk[3] = 1'b0;
    assign proc_2_data_PIPO_blk[3] = 1'b0;
    assign proc_2_start_FIFO_blk[3] = 1'b0;
    assign proc_2_TLF_FIFO_blk[3] = 1'b0;
    assign proc_2_input_sync_blk[3] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready);
    assign proc_2_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_2[3] = dl_detect_out ? proc_dep_vld_vec_2_reg[3] : (proc_2_data_FIFO_blk[3] | proc_2_data_PIPO_blk[3] | proc_2_start_FIFO_blk[3] | proc_2_TLF_FIFO_blk[3] | proc_2_input_sync_blk[3] | proc_2_output_sync_blk[3]);
    assign proc_2_data_FIFO_blk[4] = 1'b0;
    assign proc_2_data_PIPO_blk[4] = 1'b0;
    assign proc_2_start_FIFO_blk[4] = 1'b0;
    assign proc_2_TLF_FIFO_blk[4] = 1'b0;
    assign proc_2_input_sync_blk[4] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready);
    assign proc_2_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_2[4] = dl_detect_out ? proc_dep_vld_vec_2_reg[4] : (proc_2_data_FIFO_blk[4] | proc_2_data_PIPO_blk[4] | proc_2_start_FIFO_blk[4] | proc_2_TLF_FIFO_blk[4] | proc_2_input_sync_blk[4] | proc_2_output_sync_blk[4]);
    assign proc_2_data_FIFO_blk[5] = 1'b0;
    assign proc_2_data_PIPO_blk[5] = 1'b0;
    assign proc_2_start_FIFO_blk[5] = 1'b0;
    assign proc_2_TLF_FIFO_blk[5] = 1'b0;
    assign proc_2_input_sync_blk[5] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_24_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready);
    assign proc_2_output_sync_blk[5] = 1'b0;
    assign proc_dep_vld_vec_2[5] = dl_detect_out ? proc_dep_vld_vec_2_reg[5] : (proc_2_data_FIFO_blk[5] | proc_2_data_PIPO_blk[5] | proc_2_start_FIFO_blk[5] | proc_2_TLF_FIFO_blk[5] | proc_2_input_sync_blk[5] | proc_2_output_sync_blk[5]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_2_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_2_reg <= proc_dep_vld_vec_2;
        end
    end
    assign in_chan_dep_vld_vec_2[0] = dep_chan_vld_0_2;
    assign in_chan_dep_data_vec_2[8 : 0] = dep_chan_data_0_2;
    assign token_in_vec_2[0] = token_0_2;
    assign in_chan_dep_vld_vec_2[1] = dep_chan_vld_3_2;
    assign in_chan_dep_data_vec_2[17 : 9] = dep_chan_data_3_2;
    assign token_in_vec_2[1] = token_3_2;
    assign in_chan_dep_vld_vec_2[2] = dep_chan_vld_4_2;
    assign in_chan_dep_data_vec_2[26 : 18] = dep_chan_data_4_2;
    assign token_in_vec_2[2] = token_4_2;
    assign in_chan_dep_vld_vec_2[3] = dep_chan_vld_5_2;
    assign in_chan_dep_data_vec_2[35 : 27] = dep_chan_data_5_2;
    assign token_in_vec_2[3] = token_5_2;
    assign in_chan_dep_vld_vec_2[4] = dep_chan_vld_6_2;
    assign in_chan_dep_data_vec_2[44 : 36] = dep_chan_data_6_2;
    assign token_in_vec_2[4] = token_6_2;
    assign in_chan_dep_vld_vec_2[5] = dep_chan_vld_7_2;
    assign in_chan_dep_data_vec_2[53 : 45] = dep_chan_data_7_2;
    assign token_in_vec_2[5] = token_7_2;
    assign dep_chan_vld_2_6 = out_chan_dep_vld_vec_2[0];
    assign dep_chan_data_2_6 = out_chan_dep_data_2;
    assign token_2_6 = token_out_vec_2[0];
    assign dep_chan_vld_2_7 = out_chan_dep_vld_vec_2[1];
    assign dep_chan_data_2_7 = out_chan_dep_data_2;
    assign token_2_7 = token_out_vec_2[1];
    assign dep_chan_vld_2_0 = out_chan_dep_vld_vec_2[2];
    assign dep_chan_data_2_0 = out_chan_dep_data_2;
    assign token_2_0 = token_out_vec_2[2];
    assign dep_chan_vld_2_3 = out_chan_dep_vld_vec_2[3];
    assign dep_chan_data_2_3 = out_chan_dep_data_2;
    assign token_2_3 = token_out_vec_2[3];
    assign dep_chan_vld_2_4 = out_chan_dep_vld_vec_2[4];
    assign dep_chan_data_2_4 = out_chan_dep_data_2;
    assign token_2_4 = token_out_vec_2[4];
    assign dep_chan_vld_2_5 = out_chan_dep_vld_vec_2[5];
    assign dep_chan_data_2_5 = out_chan_dep_data_2;
    assign token_2_5 = token_out_vec_2[5];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0
    nbody_hls_deadlock_detect_unit #(9, 3, 6, 6) nbody_hls_deadlock_detect_unit_3 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_3),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_3),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_3),
        .token_in_vec(token_in_vec_3),
        .dl_detect_in(dl_detect_out),
        .origin(origin[3]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_3),
        .out_chan_dep_data(out_chan_dep_data_3),
        .token_out_vec(token_out_vec_3),
        .dl_detect_out(dl_in_vec[3]));

    assign proc_3_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0.streamOut_V_V_blk_n);
    assign proc_3_data_PIPO_blk[0] = 1'b0;
    assign proc_3_start_FIFO_blk[0] = 1'b0;
    assign proc_3_TLF_FIFO_blk[0] = 1'b0;
    assign proc_3_input_sync_blk[0] = 1'b0;
    assign proc_3_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_3[0] = dl_detect_out ? proc_dep_vld_vec_3_reg[0] : (proc_3_data_FIFO_blk[0] | proc_3_data_PIPO_blk[0] | proc_3_start_FIFO_blk[0] | proc_3_TLF_FIFO_blk[0] | proc_3_input_sync_blk[0] | proc_3_output_sync_blk[0]);
    assign proc_3_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0.streamOut_V_V1_blk_n);
    assign proc_3_data_PIPO_blk[1] = 1'b0;
    assign proc_3_start_FIFO_blk[1] = 1'b0;
    assign proc_3_TLF_FIFO_blk[1] = 1'b0;
    assign proc_3_input_sync_blk[1] = 1'b0;
    assign proc_3_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_3[1] = dl_detect_out ? proc_dep_vld_vec_3_reg[1] : (proc_3_data_FIFO_blk[1] | proc_3_data_PIPO_blk[1] | proc_3_start_FIFO_blk[1] | proc_3_TLF_FIFO_blk[1] | proc_3_input_sync_blk[1] | proc_3_output_sync_blk[1]);
    assign proc_3_data_FIFO_blk[2] = 1'b0;
    assign proc_3_data_PIPO_blk[2] = 1'b0;
    assign proc_3_start_FIFO_blk[2] = 1'b0;
    assign proc_3_TLF_FIFO_blk[2] = 1'b0;
    assign proc_3_input_sync_blk[2] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready);
    assign proc_3_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_3[2] = dl_detect_out ? proc_dep_vld_vec_3_reg[2] : (proc_3_data_FIFO_blk[2] | proc_3_data_PIPO_blk[2] | proc_3_start_FIFO_blk[2] | proc_3_TLF_FIFO_blk[2] | proc_3_input_sync_blk[2] | proc_3_output_sync_blk[2]);
    assign proc_3_data_FIFO_blk[3] = 1'b0;
    assign proc_3_data_PIPO_blk[3] = 1'b0;
    assign proc_3_start_FIFO_blk[3] = 1'b0;
    assign proc_3_TLF_FIFO_blk[3] = 1'b0;
    assign proc_3_input_sync_blk[3] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready);
    assign proc_3_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_3[3] = dl_detect_out ? proc_dep_vld_vec_3_reg[3] : (proc_3_data_FIFO_blk[3] | proc_3_data_PIPO_blk[3] | proc_3_start_FIFO_blk[3] | proc_3_TLF_FIFO_blk[3] | proc_3_input_sync_blk[3] | proc_3_output_sync_blk[3]);
    assign proc_3_data_FIFO_blk[4] = 1'b0;
    assign proc_3_data_PIPO_blk[4] = 1'b0;
    assign proc_3_start_FIFO_blk[4] = 1'b0;
    assign proc_3_TLF_FIFO_blk[4] = 1'b0;
    assign proc_3_input_sync_blk[4] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready);
    assign proc_3_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_3[4] = dl_detect_out ? proc_dep_vld_vec_3_reg[4] : (proc_3_data_FIFO_blk[4] | proc_3_data_PIPO_blk[4] | proc_3_start_FIFO_blk[4] | proc_3_TLF_FIFO_blk[4] | proc_3_input_sync_blk[4] | proc_3_output_sync_blk[4]);
    assign proc_3_data_FIFO_blk[5] = 1'b0;
    assign proc_3_data_PIPO_blk[5] = 1'b0;
    assign proc_3_start_FIFO_blk[5] = 1'b0;
    assign proc_3_TLF_FIFO_blk[5] = 1'b0;
    assign proc_3_input_sync_blk[5] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_25_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready);
    assign proc_3_output_sync_blk[5] = 1'b0;
    assign proc_dep_vld_vec_3[5] = dl_detect_out ? proc_dep_vld_vec_3_reg[5] : (proc_3_data_FIFO_blk[5] | proc_3_data_PIPO_blk[5] | proc_3_start_FIFO_blk[5] | proc_3_TLF_FIFO_blk[5] | proc_3_input_sync_blk[5] | proc_3_output_sync_blk[5]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_3_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_3_reg <= proc_dep_vld_vec_3;
        end
    end
    assign in_chan_dep_vld_vec_3[0] = dep_chan_vld_0_3;
    assign in_chan_dep_data_vec_3[8 : 0] = dep_chan_data_0_3;
    assign token_in_vec_3[0] = token_0_3;
    assign in_chan_dep_vld_vec_3[1] = dep_chan_vld_2_3;
    assign in_chan_dep_data_vec_3[17 : 9] = dep_chan_data_2_3;
    assign token_in_vec_3[1] = token_2_3;
    assign in_chan_dep_vld_vec_3[2] = dep_chan_vld_4_3;
    assign in_chan_dep_data_vec_3[26 : 18] = dep_chan_data_4_3;
    assign token_in_vec_3[2] = token_4_3;
    assign in_chan_dep_vld_vec_3[3] = dep_chan_vld_5_3;
    assign in_chan_dep_data_vec_3[35 : 27] = dep_chan_data_5_3;
    assign token_in_vec_3[3] = token_5_3;
    assign in_chan_dep_vld_vec_3[4] = dep_chan_vld_6_3;
    assign in_chan_dep_data_vec_3[44 : 36] = dep_chan_data_6_3;
    assign token_in_vec_3[4] = token_6_3;
    assign in_chan_dep_vld_vec_3[5] = dep_chan_vld_7_3;
    assign in_chan_dep_data_vec_3[53 : 45] = dep_chan_data_7_3;
    assign token_in_vec_3[5] = token_7_3;
    assign dep_chan_vld_3_6 = out_chan_dep_vld_vec_3[0];
    assign dep_chan_data_3_6 = out_chan_dep_data_3;
    assign token_3_6 = token_out_vec_3[0];
    assign dep_chan_vld_3_7 = out_chan_dep_vld_vec_3[1];
    assign dep_chan_data_3_7 = out_chan_dep_data_3;
    assign token_3_7 = token_out_vec_3[1];
    assign dep_chan_vld_3_0 = out_chan_dep_vld_vec_3[2];
    assign dep_chan_data_3_0 = out_chan_dep_data_3;
    assign token_3_0 = token_out_vec_3[2];
    assign dep_chan_vld_3_2 = out_chan_dep_vld_vec_3[3];
    assign dep_chan_data_3_2 = out_chan_dep_data_3;
    assign token_3_2 = token_out_vec_3[3];
    assign dep_chan_vld_3_4 = out_chan_dep_vld_vec_3[4];
    assign dep_chan_data_3_4 = out_chan_dep_data_3;
    assign token_3_4 = token_out_vec_3[4];
    assign dep_chan_vld_3_5 = out_chan_dep_vld_vec_3[5];
    assign dep_chan_data_3_5 = out_chan_dep_data_3;
    assign token_3_5 = token_out_vec_3[5];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0
    nbody_hls_deadlock_detect_unit #(9, 4, 6, 6) nbody_hls_deadlock_detect_unit_4 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_4),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_4),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_4),
        .token_in_vec(token_in_vec_4),
        .dl_detect_in(dl_detect_out),
        .origin(origin[4]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_4),
        .out_chan_dep_data(out_chan_dep_data_4),
        .token_out_vec(token_out_vec_4),
        .dl_detect_out(dl_in_vec[4]));

    assign proc_4_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0.streamOut_V_V_blk_n);
    assign proc_4_data_PIPO_blk[0] = 1'b0;
    assign proc_4_start_FIFO_blk[0] = 1'b0;
    assign proc_4_TLF_FIFO_blk[0] = 1'b0;
    assign proc_4_input_sync_blk[0] = 1'b0;
    assign proc_4_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_4[0] = dl_detect_out ? proc_dep_vld_vec_4_reg[0] : (proc_4_data_FIFO_blk[0] | proc_4_data_PIPO_blk[0] | proc_4_start_FIFO_blk[0] | proc_4_TLF_FIFO_blk[0] | proc_4_input_sync_blk[0] | proc_4_output_sync_blk[0]);
    assign proc_4_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0.streamOut_V_V1_blk_n);
    assign proc_4_data_PIPO_blk[1] = 1'b0;
    assign proc_4_start_FIFO_blk[1] = 1'b0;
    assign proc_4_TLF_FIFO_blk[1] = 1'b0;
    assign proc_4_input_sync_blk[1] = 1'b0;
    assign proc_4_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_4[1] = dl_detect_out ? proc_dep_vld_vec_4_reg[1] : (proc_4_data_FIFO_blk[1] | proc_4_data_PIPO_blk[1] | proc_4_start_FIFO_blk[1] | proc_4_TLF_FIFO_blk[1] | proc_4_input_sync_blk[1] | proc_4_output_sync_blk[1]);
    assign proc_4_data_FIFO_blk[2] = 1'b0;
    assign proc_4_data_PIPO_blk[2] = 1'b0;
    assign proc_4_start_FIFO_blk[2] = 1'b0;
    assign proc_4_TLF_FIFO_blk[2] = 1'b0;
    assign proc_4_input_sync_blk[2] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready);
    assign proc_4_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_4[2] = dl_detect_out ? proc_dep_vld_vec_4_reg[2] : (proc_4_data_FIFO_blk[2] | proc_4_data_PIPO_blk[2] | proc_4_start_FIFO_blk[2] | proc_4_TLF_FIFO_blk[2] | proc_4_input_sync_blk[2] | proc_4_output_sync_blk[2]);
    assign proc_4_data_FIFO_blk[3] = 1'b0;
    assign proc_4_data_PIPO_blk[3] = 1'b0;
    assign proc_4_start_FIFO_blk[3] = 1'b0;
    assign proc_4_TLF_FIFO_blk[3] = 1'b0;
    assign proc_4_input_sync_blk[3] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready);
    assign proc_4_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_4[3] = dl_detect_out ? proc_dep_vld_vec_4_reg[3] : (proc_4_data_FIFO_blk[3] | proc_4_data_PIPO_blk[3] | proc_4_start_FIFO_blk[3] | proc_4_TLF_FIFO_blk[3] | proc_4_input_sync_blk[3] | proc_4_output_sync_blk[3]);
    assign proc_4_data_FIFO_blk[4] = 1'b0;
    assign proc_4_data_PIPO_blk[4] = 1'b0;
    assign proc_4_start_FIFO_blk[4] = 1'b0;
    assign proc_4_TLF_FIFO_blk[4] = 1'b0;
    assign proc_4_input_sync_blk[4] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready);
    assign proc_4_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_4[4] = dl_detect_out ? proc_dep_vld_vec_4_reg[4] : (proc_4_data_FIFO_blk[4] | proc_4_data_PIPO_blk[4] | proc_4_start_FIFO_blk[4] | proc_4_TLF_FIFO_blk[4] | proc_4_input_sync_blk[4] | proc_4_output_sync_blk[4]);
    assign proc_4_data_FIFO_blk[5] = 1'b0;
    assign proc_4_data_PIPO_blk[5] = 1'b0;
    assign proc_4_start_FIFO_blk[5] = 1'b0;
    assign proc_4_TLF_FIFO_blk[5] = 1'b0;
    assign proc_4_input_sync_blk[5] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_26_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready);
    assign proc_4_output_sync_blk[5] = 1'b0;
    assign proc_dep_vld_vec_4[5] = dl_detect_out ? proc_dep_vld_vec_4_reg[5] : (proc_4_data_FIFO_blk[5] | proc_4_data_PIPO_blk[5] | proc_4_start_FIFO_blk[5] | proc_4_TLF_FIFO_blk[5] | proc_4_input_sync_blk[5] | proc_4_output_sync_blk[5]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_4_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_4_reg <= proc_dep_vld_vec_4;
        end
    end
    assign in_chan_dep_vld_vec_4[0] = dep_chan_vld_0_4;
    assign in_chan_dep_data_vec_4[8 : 0] = dep_chan_data_0_4;
    assign token_in_vec_4[0] = token_0_4;
    assign in_chan_dep_vld_vec_4[1] = dep_chan_vld_2_4;
    assign in_chan_dep_data_vec_4[17 : 9] = dep_chan_data_2_4;
    assign token_in_vec_4[1] = token_2_4;
    assign in_chan_dep_vld_vec_4[2] = dep_chan_vld_3_4;
    assign in_chan_dep_data_vec_4[26 : 18] = dep_chan_data_3_4;
    assign token_in_vec_4[2] = token_3_4;
    assign in_chan_dep_vld_vec_4[3] = dep_chan_vld_5_4;
    assign in_chan_dep_data_vec_4[35 : 27] = dep_chan_data_5_4;
    assign token_in_vec_4[3] = token_5_4;
    assign in_chan_dep_vld_vec_4[4] = dep_chan_vld_6_4;
    assign in_chan_dep_data_vec_4[44 : 36] = dep_chan_data_6_4;
    assign token_in_vec_4[4] = token_6_4;
    assign in_chan_dep_vld_vec_4[5] = dep_chan_vld_7_4;
    assign in_chan_dep_data_vec_4[53 : 45] = dep_chan_data_7_4;
    assign token_in_vec_4[5] = token_7_4;
    assign dep_chan_vld_4_6 = out_chan_dep_vld_vec_4[0];
    assign dep_chan_data_4_6 = out_chan_dep_data_4;
    assign token_4_6 = token_out_vec_4[0];
    assign dep_chan_vld_4_7 = out_chan_dep_vld_vec_4[1];
    assign dep_chan_data_4_7 = out_chan_dep_data_4;
    assign token_4_7 = token_out_vec_4[1];
    assign dep_chan_vld_4_0 = out_chan_dep_vld_vec_4[2];
    assign dep_chan_data_4_0 = out_chan_dep_data_4;
    assign token_4_0 = token_out_vec_4[2];
    assign dep_chan_vld_4_2 = out_chan_dep_vld_vec_4[3];
    assign dep_chan_data_4_2 = out_chan_dep_data_4;
    assign token_4_2 = token_out_vec_4[3];
    assign dep_chan_vld_4_3 = out_chan_dep_vld_vec_4[4];
    assign dep_chan_data_4_3 = out_chan_dep_data_4;
    assign token_4_3 = token_out_vec_4[4];
    assign dep_chan_vld_4_5 = out_chan_dep_vld_vec_4[5];
    assign dep_chan_data_4_5 = out_chan_dep_data_4;
    assign token_4_5 = token_out_vec_4[5];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0
    nbody_hls_deadlock_detect_unit #(9, 5, 6, 6) nbody_hls_deadlock_detect_unit_5 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_5),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_5),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_5),
        .token_in_vec(token_in_vec_5),
        .dl_detect_in(dl_detect_out),
        .origin(origin[5]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_5),
        .out_chan_dep_data(out_chan_dep_data_5),
        .token_out_vec(token_out_vec_5),
        .dl_detect_out(dl_in_vec[5]));

    assign proc_5_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0.streamOut_V_V_blk_n);
    assign proc_5_data_PIPO_blk[0] = 1'b0;
    assign proc_5_start_FIFO_blk[0] = 1'b0;
    assign proc_5_TLF_FIFO_blk[0] = 1'b0;
    assign proc_5_input_sync_blk[0] = 1'b0;
    assign proc_5_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_5[0] = dl_detect_out ? proc_dep_vld_vec_5_reg[0] : (proc_5_data_FIFO_blk[0] | proc_5_data_PIPO_blk[0] | proc_5_start_FIFO_blk[0] | proc_5_TLF_FIFO_blk[0] | proc_5_input_sync_blk[0] | proc_5_output_sync_blk[0]);
    assign proc_5_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0.streamOut_1_V_V_blk_n);
    assign proc_5_data_PIPO_blk[1] = 1'b0;
    assign proc_5_start_FIFO_blk[1] = 1'b0;
    assign proc_5_TLF_FIFO_blk[1] = 1'b0;
    assign proc_5_input_sync_blk[1] = 1'b0;
    assign proc_5_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_5[1] = dl_detect_out ? proc_dep_vld_vec_5_reg[1] : (proc_5_data_FIFO_blk[1] | proc_5_data_PIPO_blk[1] | proc_5_start_FIFO_blk[1] | proc_5_TLF_FIFO_blk[1] | proc_5_input_sync_blk[1] | proc_5_output_sync_blk[1]);
    assign proc_5_data_FIFO_blk[2] = 1'b0;
    assign proc_5_data_PIPO_blk[2] = 1'b0;
    assign proc_5_start_FIFO_blk[2] = 1'b0;
    assign proc_5_TLF_FIFO_blk[2] = 1'b0;
    assign proc_5_input_sync_blk[2] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_core_start_entry3_U0_ap_ready);
    assign proc_5_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_5[2] = dl_detect_out ? proc_dep_vld_vec_5_reg[2] : (proc_5_data_FIFO_blk[2] | proc_5_data_PIPO_blk[2] | proc_5_start_FIFO_blk[2] | proc_5_TLF_FIFO_blk[2] | proc_5_input_sync_blk[2] | proc_5_output_sync_blk[2]);
    assign proc_5_data_FIFO_blk[3] = 1'b0;
    assign proc_5_data_PIPO_blk[3] = 1'b0;
    assign proc_5_start_FIFO_blk[3] = 1'b0;
    assign proc_5_TLF_FIFO_blk[3] = 1'b0;
    assign proc_5_input_sync_blk[3] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_24_U0_ap_ready);
    assign proc_5_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_5[3] = dl_detect_out ? proc_dep_vld_vec_5_reg[3] : (proc_5_data_FIFO_blk[3] | proc_5_data_PIPO_blk[3] | proc_5_start_FIFO_blk[3] | proc_5_TLF_FIFO_blk[3] | proc_5_input_sync_blk[3] | proc_5_output_sync_blk[3]);
    assign proc_5_data_FIFO_blk[4] = 1'b0;
    assign proc_5_data_PIPO_blk[4] = 1'b0;
    assign proc_5_start_FIFO_blk[4] = 1'b0;
    assign proc_5_TLF_FIFO_blk[4] = 1'b0;
    assign proc_5_input_sync_blk[4] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_25_U0_ap_ready);
    assign proc_5_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_5[4] = dl_detect_out ? proc_dep_vld_vec_5_reg[4] : (proc_5_data_FIFO_blk[4] | proc_5_data_PIPO_blk[4] | proc_5_start_FIFO_blk[4] | proc_5_TLF_FIFO_blk[4] | proc_5_input_sync_blk[4] | proc_5_output_sync_blk[4]);
    assign proc_5_data_FIFO_blk[5] = 1'b0;
    assign proc_5_data_PIPO_blk[5] = 1'b0;
    assign proc_5_start_FIFO_blk[5] = 1'b0;
    assign proc_5_TLF_FIFO_blk[5] = 1'b0;
    assign proc_5_input_sync_blk[5] = 1'b0 | (grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_U0_ap_ready & grp_n_body_cu_fu_278.grp_core_start_fu_883.Axi2_MultiStreams_ap_uint_512_3750_2_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.ap_sync_Axi2_MultiStreams_ap_uint_512_3750_2_26_U0_ap_ready);
    assign proc_5_output_sync_blk[5] = 1'b0;
    assign proc_dep_vld_vec_5[5] = dl_detect_out ? proc_dep_vld_vec_5_reg[5] : (proc_5_data_FIFO_blk[5] | proc_5_data_PIPO_blk[5] | proc_5_start_FIFO_blk[5] | proc_5_TLF_FIFO_blk[5] | proc_5_input_sync_blk[5] | proc_5_output_sync_blk[5]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_5_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_5_reg <= proc_dep_vld_vec_5;
        end
    end
    assign in_chan_dep_vld_vec_5[0] = dep_chan_vld_0_5;
    assign in_chan_dep_data_vec_5[8 : 0] = dep_chan_data_0_5;
    assign token_in_vec_5[0] = token_0_5;
    assign in_chan_dep_vld_vec_5[1] = dep_chan_vld_2_5;
    assign in_chan_dep_data_vec_5[17 : 9] = dep_chan_data_2_5;
    assign token_in_vec_5[1] = token_2_5;
    assign in_chan_dep_vld_vec_5[2] = dep_chan_vld_3_5;
    assign in_chan_dep_data_vec_5[26 : 18] = dep_chan_data_3_5;
    assign token_in_vec_5[2] = token_3_5;
    assign in_chan_dep_vld_vec_5[3] = dep_chan_vld_4_5;
    assign in_chan_dep_data_vec_5[35 : 27] = dep_chan_data_4_5;
    assign token_in_vec_5[3] = token_4_5;
    assign in_chan_dep_vld_vec_5[4] = dep_chan_vld_6_5;
    assign in_chan_dep_data_vec_5[44 : 36] = dep_chan_data_6_5;
    assign token_in_vec_5[4] = token_6_5;
    assign in_chan_dep_vld_vec_5[5] = dep_chan_vld_7_5;
    assign in_chan_dep_data_vec_5[53 : 45] = dep_chan_data_7_5;
    assign token_in_vec_5[5] = token_7_5;
    assign dep_chan_vld_5_6 = out_chan_dep_vld_vec_5[0];
    assign dep_chan_data_5_6 = out_chan_dep_data_5;
    assign token_5_6 = token_out_vec_5[0];
    assign dep_chan_vld_5_7 = out_chan_dep_vld_vec_5[1];
    assign dep_chan_data_5_7 = out_chan_dep_data_5;
    assign token_5_7 = token_out_vec_5[1];
    assign dep_chan_vld_5_0 = out_chan_dep_vld_vec_5[2];
    assign dep_chan_data_5_0 = out_chan_dep_data_5;
    assign token_5_0 = token_out_vec_5[2];
    assign dep_chan_vld_5_2 = out_chan_dep_vld_vec_5[3];
    assign dep_chan_data_5_2 = out_chan_dep_data_5;
    assign token_5_2 = token_out_vec_5[3];
    assign dep_chan_vld_5_3 = out_chan_dep_vld_vec_5[4];
    assign dep_chan_data_5_3 = out_chan_dep_data_5;
    assign token_5_3 = token_out_vec_5[4];
    assign dep_chan_vld_5_4 = out_chan_dep_vld_vec_5[5];
    assign dep_chan_data_5_4 = out_chan_dep_data_5;
    assign token_5_4 = token_out_vec_5[5];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0
    nbody_hls_deadlock_detect_unit #(9, 6, 6, 6) nbody_hls_deadlock_detect_unit_6 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_6),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_6),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_6),
        .token_in_vec(token_in_vec_6),
        .dl_detect_in(dl_detect_out),
        .origin(origin[6]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_6),
        .out_chan_dep_data(out_chan_dep_data_6),
        .token_out_vec(token_out_vec_6),
        .dl_detect_out(dl_in_vec[6]));

    assign proc_6_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_x_0_V_V_blk_n);
    assign proc_6_data_PIPO_blk[0] = 1'b0;
    assign proc_6_start_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core27_U0_U.if_empty_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core27_U0_U.if_write);
    assign proc_6_TLF_FIFO_blk[0] = 1'b0;
    assign proc_6_input_sync_blk[0] = 1'b0;
    assign proc_6_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_6[0] = dl_detect_out ? proc_dep_vld_vec_6_reg[0] : (proc_6_data_FIFO_blk[0] | proc_6_data_PIPO_blk[0] | proc_6_start_FIFO_blk[0] | proc_6_TLF_FIFO_blk[0] | proc_6_input_sync_blk[0] | proc_6_output_sync_blk[0]);
    assign proc_6_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_y_0_V_V_blk_n);
    assign proc_6_data_PIPO_blk[1] = 1'b0;
    assign proc_6_start_FIFO_blk[1] = 1'b0;
    assign proc_6_TLF_FIFO_blk[1] = 1'b0;
    assign proc_6_input_sync_blk[1] = 1'b0;
    assign proc_6_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_6[1] = dl_detect_out ? proc_dep_vld_vec_6_reg[1] : (proc_6_data_FIFO_blk[1] | proc_6_data_PIPO_blk[1] | proc_6_start_FIFO_blk[1] | proc_6_TLF_FIFO_blk[1] | proc_6_input_sync_blk[1] | proc_6_output_sync_blk[1]);
    assign proc_6_data_FIFO_blk[2] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_z_0_V_V_blk_n);
    assign proc_6_data_PIPO_blk[2] = 1'b0;
    assign proc_6_start_FIFO_blk[2] = 1'b0;
    assign proc_6_TLF_FIFO_blk[2] = 1'b0;
    assign proc_6_input_sync_blk[2] = 1'b0;
    assign proc_6_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_6[2] = dl_detect_out ? proc_dep_vld_vec_6_reg[2] : (proc_6_data_FIFO_blk[2] | proc_6_data_PIPO_blk[2] | proc_6_start_FIFO_blk[2] | proc_6_TLF_FIFO_blk[2] | proc_6_input_sync_blk[2] | proc_6_output_sync_blk[2]);
    assign proc_6_data_FIFO_blk[3] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_c_0_V_V_blk_n);
    assign proc_6_data_PIPO_blk[3] = 1'b0;
    assign proc_6_start_FIFO_blk[3] = 1'b0;
    assign proc_6_TLF_FIFO_blk[3] = 1'b0;
    assign proc_6_input_sync_blk[3] = 1'b0;
    assign proc_6_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_6[3] = dl_detect_out ? proc_dep_vld_vec_6_reg[3] : (proc_6_data_FIFO_blk[3] | proc_6_data_PIPO_blk[3] | proc_6_start_FIFO_blk[3] | proc_6_TLF_FIFO_blk[3] | proc_6_input_sync_blk[3] | proc_6_output_sync_blk[3]);
    assign proc_6_data_FIFO_blk[4] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.x_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.y_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.z_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.EPS_blk_n);
    assign proc_6_data_PIPO_blk[4] = 1'b0;
    assign proc_6_start_FIFO_blk[4] = 1'b0;
    assign proc_6_TLF_FIFO_blk[4] = 1'b0;
    assign proc_6_input_sync_blk[4] = 1'b0;
    assign proc_6_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_6[4] = dl_detect_out ? proc_dep_vld_vec_6_reg[4] : (proc_6_data_FIFO_blk[4] | proc_6_data_PIPO_blk[4] | proc_6_start_FIFO_blk[4] | proc_6_TLF_FIFO_blk[4] | proc_6_input_sync_blk[4] | proc_6_output_sync_blk[4]);
    assign proc_6_data_FIFO_blk[5] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_out_x_0_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_out_y_0_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.stream_out_z_0_V_blk_n);
    assign proc_6_data_PIPO_blk[5] = 1'b0;
    assign proc_6_start_FIFO_blk[5] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_Block_split5462_proc35_U0_U.if_full_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.ap_start & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.core27_U0.real_start & (trans_in_cnt_2 == trans_out_cnt_2) & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_Block_split5462_proc35_U0_U.if_read);
    assign proc_6_TLF_FIFO_blk[5] = 1'b0;
    assign proc_6_input_sync_blk[5] = 1'b0;
    assign proc_6_output_sync_blk[5] = 1'b0;
    assign proc_dep_vld_vec_6[5] = dl_detect_out ? proc_dep_vld_vec_6_reg[5] : (proc_6_data_FIFO_blk[5] | proc_6_data_PIPO_blk[5] | proc_6_start_FIFO_blk[5] | proc_6_TLF_FIFO_blk[5] | proc_6_input_sync_blk[5] | proc_6_output_sync_blk[5]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_6_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_6_reg <= proc_dep_vld_vec_6;
        end
    end
    assign in_chan_dep_vld_vec_6[0] = dep_chan_vld_1_6;
    assign in_chan_dep_data_vec_6[8 : 0] = dep_chan_data_1_6;
    assign token_in_vec_6[0] = token_1_6;
    assign in_chan_dep_vld_vec_6[1] = dep_chan_vld_2_6;
    assign in_chan_dep_data_vec_6[17 : 9] = dep_chan_data_2_6;
    assign token_in_vec_6[1] = token_2_6;
    assign in_chan_dep_vld_vec_6[2] = dep_chan_vld_3_6;
    assign in_chan_dep_data_vec_6[26 : 18] = dep_chan_data_3_6;
    assign token_in_vec_6[2] = token_3_6;
    assign in_chan_dep_vld_vec_6[3] = dep_chan_vld_4_6;
    assign in_chan_dep_data_vec_6[35 : 27] = dep_chan_data_4_6;
    assign token_in_vec_6[3] = token_4_6;
    assign in_chan_dep_vld_vec_6[4] = dep_chan_vld_5_6;
    assign in_chan_dep_data_vec_6[44 : 36] = dep_chan_data_5_6;
    assign token_in_vec_6[4] = token_5_6;
    assign in_chan_dep_vld_vec_6[5] = dep_chan_vld_8_6;
    assign in_chan_dep_data_vec_6[53 : 45] = dep_chan_data_8_6;
    assign token_in_vec_6[5] = token_8_6;
    assign dep_chan_vld_6_2 = out_chan_dep_vld_vec_6[0];
    assign dep_chan_data_6_2 = out_chan_dep_data_6;
    assign token_6_2 = token_out_vec_6[0];
    assign dep_chan_vld_6_3 = out_chan_dep_vld_vec_6[1];
    assign dep_chan_data_6_3 = out_chan_dep_data_6;
    assign token_6_3 = token_out_vec_6[1];
    assign dep_chan_vld_6_4 = out_chan_dep_vld_vec_6[2];
    assign dep_chan_data_6_4 = out_chan_dep_data_6;
    assign token_6_4 = token_out_vec_6[2];
    assign dep_chan_vld_6_5 = out_chan_dep_vld_vec_6[3];
    assign dep_chan_data_6_5 = out_chan_dep_data_6;
    assign token_6_5 = token_out_vec_6[3];
    assign dep_chan_vld_6_1 = out_chan_dep_vld_vec_6[4];
    assign dep_chan_data_6_1 = out_chan_dep_data_6;
    assign token_6_1 = token_out_vec_6[4];
    assign dep_chan_vld_6_8 = out_chan_dep_vld_vec_6[5];
    assign dep_chan_data_6_8 = out_chan_dep_data_6;
    assign token_6_8 = token_out_vec_6[5];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0
    nbody_hls_deadlock_detect_unit #(9, 7, 6, 6) nbody_hls_deadlock_detect_unit_7 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_7),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_7),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_7),
        .token_in_vec(token_in_vec_7),
        .dl_detect_in(dl_detect_out),
        .origin(origin[7]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_7),
        .out_chan_dep_data(out_chan_dep_data_7),
        .token_out_vec(token_out_vec_7),
        .dl_detect_out(dl_in_vec[7]));

    assign proc_7_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_x_1_V_V_blk_n);
    assign proc_7_data_PIPO_blk[0] = 1'b0;
    assign proc_7_start_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core28_U0_U.if_empty_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core28_U0_U.if_write);
    assign proc_7_TLF_FIFO_blk[0] = 1'b0;
    assign proc_7_input_sync_blk[0] = 1'b0;
    assign proc_7_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_7[0] = dl_detect_out ? proc_dep_vld_vec_7_reg[0] : (proc_7_data_FIFO_blk[0] | proc_7_data_PIPO_blk[0] | proc_7_start_FIFO_blk[0] | proc_7_TLF_FIFO_blk[0] | proc_7_input_sync_blk[0] | proc_7_output_sync_blk[0]);
    assign proc_7_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_y_1_V_V_blk_n);
    assign proc_7_data_PIPO_blk[1] = 1'b0;
    assign proc_7_start_FIFO_blk[1] = 1'b0;
    assign proc_7_TLF_FIFO_blk[1] = 1'b0;
    assign proc_7_input_sync_blk[1] = 1'b0;
    assign proc_7_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_7[1] = dl_detect_out ? proc_dep_vld_vec_7_reg[1] : (proc_7_data_FIFO_blk[1] | proc_7_data_PIPO_blk[1] | proc_7_start_FIFO_blk[1] | proc_7_TLF_FIFO_blk[1] | proc_7_input_sync_blk[1] | proc_7_output_sync_blk[1]);
    assign proc_7_data_FIFO_blk[2] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_z_1_V_V_blk_n);
    assign proc_7_data_PIPO_blk[2] = 1'b0;
    assign proc_7_start_FIFO_blk[2] = 1'b0;
    assign proc_7_TLF_FIFO_blk[2] = 1'b0;
    assign proc_7_input_sync_blk[2] = 1'b0;
    assign proc_7_output_sync_blk[2] = 1'b0;
    assign proc_dep_vld_vec_7[2] = dl_detect_out ? proc_dep_vld_vec_7_reg[2] : (proc_7_data_FIFO_blk[2] | proc_7_data_PIPO_blk[2] | proc_7_start_FIFO_blk[2] | proc_7_TLF_FIFO_blk[2] | proc_7_input_sync_blk[2] | proc_7_output_sync_blk[2]);
    assign proc_7_data_FIFO_blk[3] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_c_1_V_V_blk_n);
    assign proc_7_data_PIPO_blk[3] = 1'b0;
    assign proc_7_start_FIFO_blk[3] = 1'b0;
    assign proc_7_TLF_FIFO_blk[3] = 1'b0;
    assign proc_7_input_sync_blk[3] = 1'b0;
    assign proc_7_output_sync_blk[3] = 1'b0;
    assign proc_dep_vld_vec_7[3] = dl_detect_out ? proc_dep_vld_vec_7_reg[3] : (proc_7_data_FIFO_blk[3] | proc_7_data_PIPO_blk[3] | proc_7_start_FIFO_blk[3] | proc_7_TLF_FIFO_blk[3] | proc_7_input_sync_blk[3] | proc_7_output_sync_blk[3]);
    assign proc_7_data_FIFO_blk[4] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.x_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.y_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.z_val_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.EPS_blk_n);
    assign proc_7_data_PIPO_blk[4] = 1'b0;
    assign proc_7_start_FIFO_blk[4] = 1'b0;
    assign proc_7_TLF_FIFO_blk[4] = 1'b0;
    assign proc_7_input_sync_blk[4] = 1'b0;
    assign proc_7_output_sync_blk[4] = 1'b0;
    assign proc_dep_vld_vec_7[4] = dl_detect_out ? proc_dep_vld_vec_7_reg[4] : (proc_7_data_FIFO_blk[4] | proc_7_data_PIPO_blk[4] | proc_7_start_FIFO_blk[4] | proc_7_TLF_FIFO_blk[4] | proc_7_input_sync_blk[4] | proc_7_output_sync_blk[4]);
    assign proc_7_data_FIFO_blk[5] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_out_x_1_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_out_y_1_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core28_U0.stream_out_z_1_V_blk_n);
    assign proc_7_data_PIPO_blk[5] = 1'b0;
    assign proc_7_start_FIFO_blk[5] = 1'b0;
    assign proc_7_TLF_FIFO_blk[5] = 1'b0;
    assign proc_7_input_sync_blk[5] = 1'b0;
    assign proc_7_output_sync_blk[5] = 1'b0;
    assign proc_dep_vld_vec_7[5] = dl_detect_out ? proc_dep_vld_vec_7_reg[5] : (proc_7_data_FIFO_blk[5] | proc_7_data_PIPO_blk[5] | proc_7_start_FIFO_blk[5] | proc_7_TLF_FIFO_blk[5] | proc_7_input_sync_blk[5] | proc_7_output_sync_blk[5]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_7_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_7_reg <= proc_dep_vld_vec_7;
        end
    end
    assign in_chan_dep_vld_vec_7[0] = dep_chan_vld_1_7;
    assign in_chan_dep_data_vec_7[8 : 0] = dep_chan_data_1_7;
    assign token_in_vec_7[0] = token_1_7;
    assign in_chan_dep_vld_vec_7[1] = dep_chan_vld_2_7;
    assign in_chan_dep_data_vec_7[17 : 9] = dep_chan_data_2_7;
    assign token_in_vec_7[1] = token_2_7;
    assign in_chan_dep_vld_vec_7[2] = dep_chan_vld_3_7;
    assign in_chan_dep_data_vec_7[26 : 18] = dep_chan_data_3_7;
    assign token_in_vec_7[2] = token_3_7;
    assign in_chan_dep_vld_vec_7[3] = dep_chan_vld_4_7;
    assign in_chan_dep_data_vec_7[35 : 27] = dep_chan_data_4_7;
    assign token_in_vec_7[3] = token_4_7;
    assign in_chan_dep_vld_vec_7[4] = dep_chan_vld_5_7;
    assign in_chan_dep_data_vec_7[44 : 36] = dep_chan_data_5_7;
    assign token_in_vec_7[4] = token_5_7;
    assign in_chan_dep_vld_vec_7[5] = dep_chan_vld_8_7;
    assign in_chan_dep_data_vec_7[53 : 45] = dep_chan_data_8_7;
    assign token_in_vec_7[5] = token_8_7;
    assign dep_chan_vld_7_2 = out_chan_dep_vld_vec_7[0];
    assign dep_chan_data_7_2 = out_chan_dep_data_7;
    assign token_7_2 = token_out_vec_7[0];
    assign dep_chan_vld_7_3 = out_chan_dep_vld_vec_7[1];
    assign dep_chan_data_7_3 = out_chan_dep_data_7;
    assign token_7_3 = token_out_vec_7[1];
    assign dep_chan_vld_7_4 = out_chan_dep_vld_vec_7[2];
    assign dep_chan_data_7_4 = out_chan_dep_data_7;
    assign token_7_4 = token_out_vec_7[2];
    assign dep_chan_vld_7_5 = out_chan_dep_vld_vec_7[3];
    assign dep_chan_data_7_5 = out_chan_dep_data_7;
    assign token_7_5 = token_out_vec_7[3];
    assign dep_chan_vld_7_1 = out_chan_dep_vld_vec_7[4];
    assign dep_chan_data_7_1 = out_chan_dep_data_7;
    assign token_7_1 = token_out_vec_7[4];
    assign dep_chan_vld_7_8 = out_chan_dep_vld_vec_7[5];
    assign dep_chan_data_7_8 = out_chan_dep_data_7;
    assign token_7_8 = token_out_vec_7[5];

    // Process: grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0
    nbody_hls_deadlock_detect_unit #(9, 8, 2, 2) nbody_hls_deadlock_detect_unit_8 (
        .reset(reset),
        .clock(clock),
        .proc_dep_vld_vec(proc_dep_vld_vec_8),
        .in_chan_dep_vld_vec(in_chan_dep_vld_vec_8),
        .in_chan_dep_data_vec(in_chan_dep_data_vec_8),
        .token_in_vec(token_in_vec_8),
        .dl_detect_in(dl_detect_out),
        .origin(origin[8]),
        .token_clear(token_clear),
        .out_chan_dep_vld_vec(out_chan_dep_vld_vec_8),
        .out_chan_dep_data(out_chan_dep_data_8),
        .token_out_vec(token_out_vec_8),
        .dl_detect_out(dl_in_vec[8]));

    assign proc_8_data_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.stream_out_x_0_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.stream_out_y_0_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.stream_out_z_0_V_blk_n);
    assign proc_8_data_PIPO_blk[0] = 1'b0;
    assign proc_8_start_FIFO_blk[0] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_Block_split5462_proc35_U0_U.if_empty_n & grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.ap_idle & ~grp_n_body_cu_fu_278.grp_core_start_fu_883.start_for_core_start_Block_split5462_proc35_U0_U.if_write);
    assign proc_8_TLF_FIFO_blk[0] = 1'b0;
    assign proc_8_input_sync_blk[0] = 1'b0;
    assign proc_8_output_sync_blk[0] = 1'b0;
    assign proc_dep_vld_vec_8[0] = dl_detect_out ? proc_dep_vld_vec_8_reg[0] : (proc_8_data_FIFO_blk[0] | proc_8_data_PIPO_blk[0] | proc_8_start_FIFO_blk[0] | proc_8_TLF_FIFO_blk[0] | proc_8_input_sync_blk[0] | proc_8_output_sync_blk[0]);
    assign proc_8_data_FIFO_blk[1] = 1'b0 | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.stream_out_x_1_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.stream_out_y_1_V_blk_n) | (~grp_n_body_cu_fu_278.grp_core_start_fu_883.core_start_Block_split5462_proc35_U0.stream_out_z_1_V_blk_n);
    assign proc_8_data_PIPO_blk[1] = 1'b0;
    assign proc_8_start_FIFO_blk[1] = 1'b0;
    assign proc_8_TLF_FIFO_blk[1] = 1'b0;
    assign proc_8_input_sync_blk[1] = 1'b0;
    assign proc_8_output_sync_blk[1] = 1'b0;
    assign proc_dep_vld_vec_8[1] = dl_detect_out ? proc_dep_vld_vec_8_reg[1] : (proc_8_data_FIFO_blk[1] | proc_8_data_PIPO_blk[1] | proc_8_start_FIFO_blk[1] | proc_8_TLF_FIFO_blk[1] | proc_8_input_sync_blk[1] | proc_8_output_sync_blk[1]);
    always @ (negedge reset or posedge clock) begin
        if (~reset) begin
            proc_dep_vld_vec_8_reg <= 'b0;
        end
        else begin
            proc_dep_vld_vec_8_reg <= proc_dep_vld_vec_8;
        end
    end
    assign in_chan_dep_vld_vec_8[0] = dep_chan_vld_6_8;
    assign in_chan_dep_data_vec_8[8 : 0] = dep_chan_data_6_8;
    assign token_in_vec_8[0] = token_6_8;
    assign in_chan_dep_vld_vec_8[1] = dep_chan_vld_7_8;
    assign in_chan_dep_data_vec_8[17 : 9] = dep_chan_data_7_8;
    assign token_in_vec_8[1] = token_7_8;
    assign dep_chan_vld_8_6 = out_chan_dep_vld_vec_8[0];
    assign dep_chan_data_8_6 = out_chan_dep_data_8;
    assign token_8_6 = token_out_vec_8[0];
    assign dep_chan_vld_8_7 = out_chan_dep_vld_vec_8[1];
    assign dep_chan_data_8_7 = out_chan_dep_data_8;
    assign token_8_7 = token_out_vec_8[1];


`include "nbody_hls_deadlock_report_unit.vh"
