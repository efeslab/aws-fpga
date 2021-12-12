// ==============================================================
// RTL generated by Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Version: 2020.2
// Copyright (C) Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// 
// ===========================================================

`timescale 1 ns / 1 ps 

module optical_flow_outer_product (
        ap_clk,
        ap_rst,
        ap_start,
        start_full_n,
        ap_done,
        ap_continue,
        ap_idle,
        ap_ready,
        start_out,
        start_write,
        filtered_gradient_x_V_dout,
        filtered_gradient_x_V_empty_n,
        filtered_gradient_x_V_read,
        filtered_gradient_y_V_dout,
        filtered_gradient_y_V_empty_n,
        filtered_gradient_y_V_read,
        filtered_gradient_z_V_dout,
        filtered_gradient_z_V_empty_n,
        filtered_gradient_z_V_read,
        out_product_din,
        out_product_full_n,
        out_product_write
);

parameter    ap_ST_fsm_state1 = 3'd1;
parameter    ap_ST_fsm_pp0_stage0 = 3'd2;
parameter    ap_ST_fsm_state7 = 3'd4;

input   ap_clk;
input   ap_rst;
input   ap_start;
input   start_full_n;
output   ap_done;
input   ap_continue;
output   ap_idle;
output   ap_ready;
output   start_out;
output   start_write;
input  [31:0] filtered_gradient_x_V_dout;
input   filtered_gradient_x_V_empty_n;
output   filtered_gradient_x_V_read;
input  [31:0] filtered_gradient_y_V_dout;
input   filtered_gradient_y_V_empty_n;
output   filtered_gradient_y_V_read;
input  [31:0] filtered_gradient_z_V_dout;
input   filtered_gradient_z_V_empty_n;
output   filtered_gradient_z_V_read;
output  [191:0] out_product_din;
input   out_product_full_n;
output   out_product_write;

reg ap_done;
reg ap_idle;
reg start_write;
reg filtered_gradient_x_V_read;
reg filtered_gradient_y_V_read;
reg filtered_gradient_z_V_read;
reg out_product_write;

reg    real_start;
reg    start_once_reg;
reg    ap_done_reg;
(* fsm_encoding = "none" *) reg   [2:0] ap_CS_fsm;
wire    ap_CS_fsm_state1;
reg    internal_ap_ready;
reg    filtered_gradient_x_V_blk_n;
wire    ap_CS_fsm_pp0_stage0;
reg    ap_enable_reg_pp0_iter1;
wire    ap_block_pp0_stage0;
reg   [0:0] icmp_ln234_reg_286;
reg    filtered_gradient_y_V_blk_n;
reg    filtered_gradient_z_V_blk_n;
reg    out_product_blk_n;
reg    ap_enable_reg_pp0_iter4;
reg   [0:0] icmp_ln234_reg_286_pp0_iter3_reg;
reg   [18:0] indvar_flatten_reg_79;
wire   [18:0] add_ln234_fu_90_p2;
reg    ap_enable_reg_pp0_iter0;
wire    ap_block_state2_pp0_stage0_iter0;
reg    ap_block_state3_pp0_stage0_iter1;
wire    ap_block_state4_pp0_stage0_iter2;
wire    ap_block_state5_pp0_stage0_iter3;
reg    ap_block_state6_pp0_stage0_iter4;
reg    ap_block_pp0_stage0_11001;
wire   [0:0] icmp_ln234_fu_96_p2;
reg   [0:0] icmp_ln234_reg_286_pp0_iter1_reg;
reg   [0:0] icmp_ln234_reg_286_pp0_iter2_reg;
wire  signed [35:0] sext_ln1115_fu_132_p1;
wire  signed [35:0] sext_ln1115_1_fu_136_p1;
wire  signed [35:0] sext_ln1115_2_fu_140_p1;
reg    ap_block_state1;
reg    ap_block_pp0_stage0_subdone;
reg    ap_condition_pp0_exit_iter0_state2;
reg    ap_enable_reg_pp0_iter2;
reg    ap_enable_reg_pp0_iter3;
reg    ap_block_pp0_stage0_01001;
wire   [17:0] r_V_fu_102_p4;
wire   [17:0] r_V_2_fu_112_p4;
wire   [17:0] r_V_4_fu_122_p4;
wire  signed [35:0] grp_fu_239_p2;
wire   [30:0] out_fu_144_p4;
wire  signed [35:0] grp_fu_246_p2;
wire   [30:0] out_1_fu_157_p4;
wire  signed [35:0] grp_fu_253_p2;
wire  signed [35:0] grp_fu_260_p2;
wire   [30:0] out_2_fu_179_p4;
wire  signed [35:0] grp_fu_267_p2;
wire  signed [35:0] grp_fu_274_p2;
wire   [30:0] trunc_ln_fu_170_p4;
wire   [30:0] trunc_ln708_4_fu_192_p4;
wire   [30:0] trunc_ln708_5_fu_201_p4;
wire  signed [31:0] sext_ln250_1_fu_214_p1;
wire  signed [31:0] sext_ln708_2_fu_188_p1;
wire  signed [31:0] sext_ln250_fu_210_p1;
wire  signed [31:0] sext_ln708_1_fu_166_p1;
wire  signed [31:0] sext_ln708_fu_153_p1;
wire   [190:0] tmp_fu_218_p7;
wire  signed [17:0] grp_fu_239_p0;
wire  signed [17:0] grp_fu_239_p1;
wire  signed [17:0] grp_fu_246_p0;
wire  signed [17:0] grp_fu_246_p1;
wire  signed [17:0] grp_fu_253_p0;
wire  signed [17:0] grp_fu_253_p1;
wire  signed [17:0] grp_fu_260_p0;
wire  signed [17:0] grp_fu_260_p1;
wire  signed [17:0] grp_fu_267_p0;
wire  signed [17:0] grp_fu_267_p1;
wire  signed [17:0] grp_fu_274_p0;
wire  signed [17:0] grp_fu_274_p1;
reg    grp_fu_239_ce;
reg    grp_fu_246_ce;
reg    grp_fu_253_ce;
reg    grp_fu_260_ce;
reg    grp_fu_267_ce;
reg    grp_fu_274_ce;
wire    ap_CS_fsm_state7;
reg   [2:0] ap_NS_fsm;
reg    ap_idle_pp0;
wire    ap_enable_pp0;
wire    ap_ce_reg;

// power-on initialization
initial begin
#0 start_once_reg = 1'b0;
#0 ap_done_reg = 1'b0;
#0 ap_CS_fsm = 3'd1;
#0 ap_enable_reg_pp0_iter1 = 1'b0;
#0 ap_enable_reg_pp0_iter4 = 1'b0;
#0 ap_enable_reg_pp0_iter0 = 1'b0;
#0 ap_enable_reg_pp0_iter2 = 1'b0;
#0 ap_enable_reg_pp0_iter3 = 1'b0;
end

optical_flow_mul_mul_18s_18s_36_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 18 ),
    .din1_WIDTH( 18 ),
    .dout_WIDTH( 36 ))
mul_mul_18s_18s_36_4_1_U87(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_239_p0),
    .din1(grp_fu_239_p1),
    .ce(grp_fu_239_ce),
    .dout(grp_fu_239_p2)
);

optical_flow_mul_mul_18s_18s_36_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 18 ),
    .din1_WIDTH( 18 ),
    .dout_WIDTH( 36 ))
mul_mul_18s_18s_36_4_1_U88(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_246_p0),
    .din1(grp_fu_246_p1),
    .ce(grp_fu_246_ce),
    .dout(grp_fu_246_p2)
);

optical_flow_mul_mul_18s_18s_36_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 18 ),
    .din1_WIDTH( 18 ),
    .dout_WIDTH( 36 ))
mul_mul_18s_18s_36_4_1_U89(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_253_p0),
    .din1(grp_fu_253_p1),
    .ce(grp_fu_253_ce),
    .dout(grp_fu_253_p2)
);

optical_flow_mul_mul_18s_18s_36_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 18 ),
    .din1_WIDTH( 18 ),
    .dout_WIDTH( 36 ))
mul_mul_18s_18s_36_4_1_U90(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_260_p0),
    .din1(grp_fu_260_p1),
    .ce(grp_fu_260_ce),
    .dout(grp_fu_260_p2)
);

optical_flow_mul_mul_18s_18s_36_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 18 ),
    .din1_WIDTH( 18 ),
    .dout_WIDTH( 36 ))
mul_mul_18s_18s_36_4_1_U91(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_267_p0),
    .din1(grp_fu_267_p1),
    .ce(grp_fu_267_ce),
    .dout(grp_fu_267_p2)
);

optical_flow_mul_mul_18s_18s_36_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 18 ),
    .din1_WIDTH( 18 ),
    .dout_WIDTH( 36 ))
mul_mul_18s_18s_36_4_1_U92(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_274_p0),
    .din1(grp_fu_274_p1),
    .ce(grp_fu_274_ce),
    .dout(grp_fu_274_p2)
);

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_CS_fsm <= ap_ST_fsm_state1;
    end else begin
        ap_CS_fsm <= ap_NS_fsm;
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_done_reg <= 1'b0;
    end else begin
        if ((ap_continue == 1'b1)) begin
            ap_done_reg <= 1'b0;
        end else if ((1'b1 == ap_CS_fsm_state7)) begin
            ap_done_reg <= 1'b1;
        end
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_enable_reg_pp0_iter0 <= 1'b0;
    end else begin
        if (((1'b0 == ap_block_pp0_stage0_subdone) & (1'b1 == ap_CS_fsm_pp0_stage0) & (1'b1 == ap_condition_pp0_exit_iter0_state2))) begin
            ap_enable_reg_pp0_iter0 <= 1'b0;
        end else if ((~((real_start == 1'b0) | (ap_done_reg == 1'b1)) & (1'b1 == ap_CS_fsm_state1))) begin
            ap_enable_reg_pp0_iter0 <= 1'b1;
        end
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_enable_reg_pp0_iter1 <= 1'b0;
    end else begin
        if ((1'b0 == ap_block_pp0_stage0_subdone)) begin
            if ((1'b1 == ap_condition_pp0_exit_iter0_state2)) begin
                ap_enable_reg_pp0_iter1 <= (1'b1 ^ ap_condition_pp0_exit_iter0_state2);
            end else if ((1'b1 == 1'b1)) begin
                ap_enable_reg_pp0_iter1 <= ap_enable_reg_pp0_iter0;
            end
        end
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_enable_reg_pp0_iter2 <= 1'b0;
    end else begin
        if ((1'b0 == ap_block_pp0_stage0_subdone)) begin
            ap_enable_reg_pp0_iter2 <= ap_enable_reg_pp0_iter1;
        end
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_enable_reg_pp0_iter3 <= 1'b0;
    end else begin
        if ((1'b0 == ap_block_pp0_stage0_subdone)) begin
            ap_enable_reg_pp0_iter3 <= ap_enable_reg_pp0_iter2;
        end
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        ap_enable_reg_pp0_iter4 <= 1'b0;
    end else begin
        if ((1'b0 == ap_block_pp0_stage0_subdone)) begin
            ap_enable_reg_pp0_iter4 <= ap_enable_reg_pp0_iter3;
        end else if ((~((real_start == 1'b0) | (ap_done_reg == 1'b1)) & (1'b1 == ap_CS_fsm_state1))) begin
            ap_enable_reg_pp0_iter4 <= 1'b0;
        end
    end
end

always @ (posedge ap_clk) begin
    if (ap_rst == 1'b1) begin
        start_once_reg <= 1'b0;
    end else begin
        if (((real_start == 1'b1) & (internal_ap_ready == 1'b0))) begin
            start_once_reg <= 1'b1;
        end else if ((internal_ap_ready == 1'b1)) begin
            start_once_reg <= 1'b0;
        end
    end
end

always @ (posedge ap_clk) begin
    if (((ap_enable_reg_pp0_iter0 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0) & (icmp_ln234_fu_96_p2 == 1'd0))) begin
        indvar_flatten_reg_79 <= add_ln234_fu_90_p2;
    end else if ((~((real_start == 1'b0) | (ap_done_reg == 1'b1)) & (1'b1 == ap_CS_fsm_state1))) begin
        indvar_flatten_reg_79 <= 19'd0;
    end
end

always @ (posedge ap_clk) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        icmp_ln234_reg_286 <= icmp_ln234_fu_96_p2;
        icmp_ln234_reg_286_pp0_iter1_reg <= icmp_ln234_reg_286;
    end
end

always @ (posedge ap_clk) begin
    if ((1'b0 == ap_block_pp0_stage0_11001)) begin
        icmp_ln234_reg_286_pp0_iter2_reg <= icmp_ln234_reg_286_pp0_iter1_reg;
        icmp_ln234_reg_286_pp0_iter3_reg <= icmp_ln234_reg_286_pp0_iter2_reg;
    end
end

always @ (*) begin
    if ((icmp_ln234_fu_96_p2 == 1'd1)) begin
        ap_condition_pp0_exit_iter0_state2 = 1'b1;
    end else begin
        ap_condition_pp0_exit_iter0_state2 = 1'b0;
    end
end

always @ (*) begin
    if ((1'b1 == ap_CS_fsm_state7)) begin
        ap_done = 1'b1;
    end else begin
        ap_done = ap_done_reg;
    end
end

always @ (*) begin
    if (((real_start == 1'b0) & (1'b1 == ap_CS_fsm_state1))) begin
        ap_idle = 1'b1;
    end else begin
        ap_idle = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter0 == 1'b0) & (ap_enable_reg_pp0_iter4 == 1'b0) & (ap_enable_reg_pp0_iter1 == 1'b0) & (ap_enable_reg_pp0_iter3 == 1'b0) & (ap_enable_reg_pp0_iter2 == 1'b0))) begin
        ap_idle_pp0 = 1'b1;
    end else begin
        ap_idle_pp0 = 1'b0;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286 == 1'd0) & (1'b0 == ap_block_pp0_stage0) & (ap_enable_reg_pp0_iter1 == 1'b1) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        filtered_gradient_x_V_blk_n = filtered_gradient_x_V_empty_n;
    end else begin
        filtered_gradient_x_V_blk_n = 1'b1;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (ap_enable_reg_pp0_iter1 == 1'b1) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        filtered_gradient_x_V_read = 1'b1;
    end else begin
        filtered_gradient_x_V_read = 1'b0;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286 == 1'd0) & (1'b0 == ap_block_pp0_stage0) & (ap_enable_reg_pp0_iter1 == 1'b1) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        filtered_gradient_y_V_blk_n = filtered_gradient_y_V_empty_n;
    end else begin
        filtered_gradient_y_V_blk_n = 1'b1;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (ap_enable_reg_pp0_iter1 == 1'b1) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        filtered_gradient_y_V_read = 1'b1;
    end else begin
        filtered_gradient_y_V_read = 1'b0;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286 == 1'd0) & (1'b0 == ap_block_pp0_stage0) & (ap_enable_reg_pp0_iter1 == 1'b1) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        filtered_gradient_z_V_blk_n = filtered_gradient_z_V_empty_n;
    end else begin
        filtered_gradient_z_V_blk_n = 1'b1;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (ap_enable_reg_pp0_iter1 == 1'b1) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        filtered_gradient_z_V_read = 1'b1;
    end else begin
        filtered_gradient_z_V_read = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        grp_fu_239_ce = 1'b1;
    end else begin
        grp_fu_239_ce = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        grp_fu_246_ce = 1'b1;
    end else begin
        grp_fu_246_ce = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        grp_fu_253_ce = 1'b1;
    end else begin
        grp_fu_253_ce = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        grp_fu_260_ce = 1'b1;
    end else begin
        grp_fu_260_ce = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        grp_fu_267_ce = 1'b1;
    end else begin
        grp_fu_267_ce = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        grp_fu_274_ce = 1'b1;
    end else begin
        grp_fu_274_ce = 1'b0;
    end
end

always @ (*) begin
    if ((1'b1 == ap_CS_fsm_state7)) begin
        internal_ap_ready = 1'b1;
    end else begin
        internal_ap_ready = 1'b0;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286_pp0_iter3_reg == 1'd0) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0))) begin
        out_product_blk_n = out_product_full_n;
    end else begin
        out_product_blk_n = 1'b1;
    end
end

always @ (*) begin
    if (((icmp_ln234_reg_286_pp0_iter3_reg == 1'd0) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        out_product_write = 1'b1;
    end else begin
        out_product_write = 1'b0;
    end
end

always @ (*) begin
    if (((start_once_reg == 1'b0) & (start_full_n == 1'b0))) begin
        real_start = 1'b0;
    end else begin
        real_start = ap_start;
    end
end

always @ (*) begin
    if (((real_start == 1'b1) & (start_once_reg == 1'b0))) begin
        start_write = 1'b1;
    end else begin
        start_write = 1'b0;
    end
end

always @ (*) begin
    case (ap_CS_fsm)
        ap_ST_fsm_state1 : begin
            if ((~((real_start == 1'b0) | (ap_done_reg == 1'b1)) & (1'b1 == ap_CS_fsm_state1))) begin
                ap_NS_fsm = ap_ST_fsm_pp0_stage0;
            end else begin
                ap_NS_fsm = ap_ST_fsm_state1;
            end
        end
        ap_ST_fsm_pp0_stage0 : begin
            if ((~((ap_enable_reg_pp0_iter0 == 1'b1) & (1'b0 == ap_block_pp0_stage0_subdone) & (ap_enable_reg_pp0_iter1 == 1'b0) & (icmp_ln234_fu_96_p2 == 1'd1)) & ~((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_subdone) & (ap_enable_reg_pp0_iter3 == 1'b0)))) begin
                ap_NS_fsm = ap_ST_fsm_pp0_stage0;
            end else if ((((ap_enable_reg_pp0_iter0 == 1'b1) & (1'b0 == ap_block_pp0_stage0_subdone) & (ap_enable_reg_pp0_iter1 == 1'b0) & (icmp_ln234_fu_96_p2 == 1'd1)) | ((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_subdone) & (ap_enable_reg_pp0_iter3 == 1'b0)))) begin
                ap_NS_fsm = ap_ST_fsm_state7;
            end else begin
                ap_NS_fsm = ap_ST_fsm_pp0_stage0;
            end
        end
        ap_ST_fsm_state7 : begin
            ap_NS_fsm = ap_ST_fsm_state1;
        end
        default : begin
            ap_NS_fsm = 'bx;
        end
    endcase
end

assign add_ln234_fu_90_p2 = (indvar_flatten_reg_79 + 19'd1);

assign ap_CS_fsm_pp0_stage0 = ap_CS_fsm[32'd1];

assign ap_CS_fsm_state1 = ap_CS_fsm[32'd0];

assign ap_CS_fsm_state7 = ap_CS_fsm[32'd2];

assign ap_block_pp0_stage0 = ~(1'b1 == 1'b1);

always @ (*) begin
    ap_block_pp0_stage0_01001 = (((icmp_ln234_reg_286_pp0_iter3_reg == 1'd0) & (ap_enable_reg_pp0_iter4 == 1'b1) & (out_product_full_n == 1'b0)) | ((ap_enable_reg_pp0_iter1 == 1'b1) & (((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_z_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_y_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_x_V_empty_n == 1'b0)))));
end

always @ (*) begin
    ap_block_pp0_stage0_11001 = (((icmp_ln234_reg_286_pp0_iter3_reg == 1'd0) & (ap_enable_reg_pp0_iter4 == 1'b1) & (out_product_full_n == 1'b0)) | ((ap_enable_reg_pp0_iter1 == 1'b1) & (((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_z_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_y_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_x_V_empty_n == 1'b0)))));
end

always @ (*) begin
    ap_block_pp0_stage0_subdone = (((icmp_ln234_reg_286_pp0_iter3_reg == 1'd0) & (ap_enable_reg_pp0_iter4 == 1'b1) & (out_product_full_n == 1'b0)) | ((ap_enable_reg_pp0_iter1 == 1'b1) & (((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_z_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_y_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_x_V_empty_n == 1'b0)))));
end

always @ (*) begin
    ap_block_state1 = ((real_start == 1'b0) | (ap_done_reg == 1'b1));
end

assign ap_block_state2_pp0_stage0_iter0 = ~(1'b1 == 1'b1);

always @ (*) begin
    ap_block_state3_pp0_stage0_iter1 = (((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_z_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_y_V_empty_n == 1'b0)) | ((icmp_ln234_reg_286 == 1'd0) & (filtered_gradient_x_V_empty_n == 1'b0)));
end

assign ap_block_state4_pp0_stage0_iter2 = ~(1'b1 == 1'b1);

assign ap_block_state5_pp0_stage0_iter3 = ~(1'b1 == 1'b1);

always @ (*) begin
    ap_block_state6_pp0_stage0_iter4 = ((icmp_ln234_reg_286_pp0_iter3_reg == 1'd0) & (out_product_full_n == 1'b0));
end

assign ap_enable_pp0 = (ap_idle_pp0 ^ 1'b1);

assign ap_ready = internal_ap_ready;

assign grp_fu_239_p0 = sext_ln1115_fu_132_p1;

assign grp_fu_239_p1 = sext_ln1115_fu_132_p1;

assign grp_fu_246_p0 = sext_ln1115_1_fu_136_p1;

assign grp_fu_246_p1 = sext_ln1115_1_fu_136_p1;

assign grp_fu_253_p0 = sext_ln1115_2_fu_140_p1;

assign grp_fu_253_p1 = sext_ln1115_2_fu_140_p1;

assign grp_fu_260_p0 = sext_ln1115_1_fu_136_p1;

assign grp_fu_260_p1 = sext_ln1115_fu_132_p1;

assign grp_fu_267_p0 = sext_ln1115_2_fu_140_p1;

assign grp_fu_267_p1 = sext_ln1115_fu_132_p1;

assign grp_fu_274_p0 = sext_ln1115_2_fu_140_p1;

assign grp_fu_274_p1 = sext_ln1115_1_fu_136_p1;

assign icmp_ln234_fu_96_p2 = ((indvar_flatten_reg_79 == 19'd446464) ? 1'b1 : 1'b0);

assign out_1_fu_157_p4 = {{grp_fu_246_p2[35:5]}};

assign out_2_fu_179_p4 = {{grp_fu_260_p2[35:5]}};

assign out_fu_144_p4 = {{grp_fu_239_p2[35:5]}};

assign out_product_din = $signed(tmp_fu_218_p7);

assign r_V_2_fu_112_p4 = {{filtered_gradient_y_V_dout[31:14]}};

assign r_V_4_fu_122_p4 = {{filtered_gradient_z_V_dout[31:14]}};

assign r_V_fu_102_p4 = {{filtered_gradient_x_V_dout[31:14]}};

assign sext_ln1115_1_fu_136_p1 = $signed(r_V_2_fu_112_p4);

assign sext_ln1115_2_fu_140_p1 = $signed(r_V_4_fu_122_p4);

assign sext_ln1115_fu_132_p1 = $signed(r_V_fu_102_p4);

assign sext_ln250_1_fu_214_p1 = $signed(trunc_ln708_4_fu_192_p4);

assign sext_ln250_fu_210_p1 = $signed(trunc_ln_fu_170_p4);

assign sext_ln708_1_fu_166_p1 = $signed(out_1_fu_157_p4);

assign sext_ln708_2_fu_188_p1 = $signed(out_2_fu_179_p4);

assign sext_ln708_fu_153_p1 = $signed(out_fu_144_p4);

assign start_out = real_start;

assign tmp_fu_218_p7 = {{{{{{trunc_ln708_5_fu_201_p4}, {sext_ln250_1_fu_214_p1}}, {sext_ln708_2_fu_188_p1}}, {sext_ln250_fu_210_p1}}, {sext_ln708_1_fu_166_p1}}, {sext_ln708_fu_153_p1}};

assign trunc_ln708_4_fu_192_p4 = {{grp_fu_267_p2[35:5]}};

assign trunc_ln708_5_fu_201_p4 = {{grp_fu_274_p2[35:5]}};

assign trunc_ln_fu_170_p4 = {{grp_fu_253_p2[35:5]}};

endmodule //optical_flow_outer_product