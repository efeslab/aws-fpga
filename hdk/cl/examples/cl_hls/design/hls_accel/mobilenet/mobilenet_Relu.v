// ==============================================================
// RTL generated by Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Version: 2020.2
// Copyright (C) Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// 
// ===========================================================

`timescale 1 ns / 1 ps 

module mobilenet_Relu (
        ap_clk,
        ap_rst,
        ap_start,
        ap_done,
        ap_idle,
        ap_ready,
        buf_r_address0,
        buf_r_ce0,
        buf_r_we0,
        buf_r_d0,
        buf_r_address1,
        buf_r_ce1,
        buf_r_q1,
        buf1_address0,
        buf1_ce0,
        buf1_we0,
        buf1_d0,
        buf1_address1,
        buf1_ce1,
        buf1_q1,
        buf2_address0,
        buf2_ce0,
        buf2_we0,
        buf2_d0,
        buf2_address1,
        buf2_ce1,
        buf2_q1,
        buf3_address0,
        buf3_ce0,
        buf3_we0,
        buf3_d0,
        buf3_address1,
        buf3_ce1,
        buf3_q1,
        buf4_address0,
        buf4_ce0,
        buf4_we0,
        buf4_d0,
        buf4_address1,
        buf4_ce1,
        buf4_q1,
        buf5_address0,
        buf5_ce0,
        buf5_we0,
        buf5_d0,
        buf5_address1,
        buf5_ce1,
        buf5_q1,
        buf6_address0,
        buf6_ce0,
        buf6_we0,
        buf6_d0,
        buf6_address1,
        buf6_ce1,
        buf6_q1,
        buf7_address0,
        buf7_ce0,
        buf7_we0,
        buf7_d0,
        buf7_address1,
        buf7_ce1,
        buf7_q1,
        buf8_address0,
        buf8_ce0,
        buf8_we0,
        buf8_d0,
        buf8_address1,
        buf8_ce1,
        buf8_q1,
        buf9_address0,
        buf9_ce0,
        buf9_we0,
        buf9_d0,
        buf9_address1,
        buf9_ce1,
        buf9_q1,
        buf10_address0,
        buf10_ce0,
        buf10_we0,
        buf10_d0,
        buf10_address1,
        buf10_ce1,
        buf10_q1,
        buf11_address0,
        buf11_ce0,
        buf11_we0,
        buf11_d0,
        buf11_address1,
        buf11_ce1,
        buf11_q1,
        buf12_address0,
        buf12_ce0,
        buf12_we0,
        buf12_d0,
        buf12_address1,
        buf12_ce1,
        buf12_q1,
        buf13_address0,
        buf13_ce0,
        buf13_we0,
        buf13_d0,
        buf13_address1,
        buf13_ce1,
        buf13_q1,
        buf14_address0,
        buf14_ce0,
        buf14_we0,
        buf14_d0,
        buf14_address1,
        buf14_ce1,
        buf14_q1,
        buf15_address0,
        buf15_ce0,
        buf15_we0,
        buf15_d0,
        buf15_address1,
        buf15_ce1,
        buf15_q1
);

parameter    ap_ST_fsm_state1 = 3'd1;
parameter    ap_ST_fsm_pp0_stage0 = 3'd2;
parameter    ap_ST_fsm_state7 = 3'd4;

input   ap_clk;
input   ap_rst;
input   ap_start;
output   ap_done;
output   ap_idle;
output   ap_ready;
output  [9:0] buf_r_address0;
output   buf_r_ce0;
output   buf_r_we0;
output  [15:0] buf_r_d0;
output  [9:0] buf_r_address1;
output   buf_r_ce1;
input  [15:0] buf_r_q1;
output  [9:0] buf1_address0;
output   buf1_ce0;
output   buf1_we0;
output  [15:0] buf1_d0;
output  [9:0] buf1_address1;
output   buf1_ce1;
input  [15:0] buf1_q1;
output  [9:0] buf2_address0;
output   buf2_ce0;
output   buf2_we0;
output  [15:0] buf2_d0;
output  [9:0] buf2_address1;
output   buf2_ce1;
input  [15:0] buf2_q1;
output  [9:0] buf3_address0;
output   buf3_ce0;
output   buf3_we0;
output  [15:0] buf3_d0;
output  [9:0] buf3_address1;
output   buf3_ce1;
input  [15:0] buf3_q1;
output  [9:0] buf4_address0;
output   buf4_ce0;
output   buf4_we0;
output  [15:0] buf4_d0;
output  [9:0] buf4_address1;
output   buf4_ce1;
input  [15:0] buf4_q1;
output  [9:0] buf5_address0;
output   buf5_ce0;
output   buf5_we0;
output  [15:0] buf5_d0;
output  [9:0] buf5_address1;
output   buf5_ce1;
input  [15:0] buf5_q1;
output  [9:0] buf6_address0;
output   buf6_ce0;
output   buf6_we0;
output  [15:0] buf6_d0;
output  [9:0] buf6_address1;
output   buf6_ce1;
input  [15:0] buf6_q1;
output  [9:0] buf7_address0;
output   buf7_ce0;
output   buf7_we0;
output  [15:0] buf7_d0;
output  [9:0] buf7_address1;
output   buf7_ce1;
input  [15:0] buf7_q1;
output  [9:0] buf8_address0;
output   buf8_ce0;
output   buf8_we0;
output  [15:0] buf8_d0;
output  [9:0] buf8_address1;
output   buf8_ce1;
input  [15:0] buf8_q1;
output  [9:0] buf9_address0;
output   buf9_ce0;
output   buf9_we0;
output  [15:0] buf9_d0;
output  [9:0] buf9_address1;
output   buf9_ce1;
input  [15:0] buf9_q1;
output  [9:0] buf10_address0;
output   buf10_ce0;
output   buf10_we0;
output  [15:0] buf10_d0;
output  [9:0] buf10_address1;
output   buf10_ce1;
input  [15:0] buf10_q1;
output  [9:0] buf11_address0;
output   buf11_ce0;
output   buf11_we0;
output  [15:0] buf11_d0;
output  [9:0] buf11_address1;
output   buf11_ce1;
input  [15:0] buf11_q1;
output  [9:0] buf12_address0;
output   buf12_ce0;
output   buf12_we0;
output  [15:0] buf12_d0;
output  [9:0] buf12_address1;
output   buf12_ce1;
input  [15:0] buf12_q1;
output  [9:0] buf13_address0;
output   buf13_ce0;
output   buf13_we0;
output  [15:0] buf13_d0;
output  [9:0] buf13_address1;
output   buf13_ce1;
input  [15:0] buf13_q1;
output  [9:0] buf14_address0;
output   buf14_ce0;
output   buf14_we0;
output  [15:0] buf14_d0;
output  [9:0] buf14_address1;
output   buf14_ce1;
input  [15:0] buf14_q1;
output  [9:0] buf15_address0;
output   buf15_ce0;
output   buf15_we0;
output  [15:0] buf15_d0;
output  [9:0] buf15_address1;
output   buf15_ce1;
input  [15:0] buf15_q1;

reg ap_done;
reg ap_idle;
reg ap_ready;
reg buf_r_ce0;
reg buf_r_we0;
reg buf_r_ce1;
reg buf1_ce0;
reg buf1_we0;
reg buf1_ce1;
reg buf2_ce0;
reg buf2_we0;
reg buf2_ce1;
reg buf3_ce0;
reg buf3_we0;
reg buf3_ce1;
reg buf4_ce0;
reg buf4_we0;
reg buf4_ce1;
reg buf5_ce0;
reg buf5_we0;
reg buf5_ce1;
reg buf6_ce0;
reg buf6_we0;
reg buf6_ce1;
reg buf7_ce0;
reg buf7_we0;
reg buf7_ce1;
reg buf8_ce0;
reg buf8_we0;
reg buf8_ce1;
reg buf9_ce0;
reg buf9_we0;
reg buf9_ce1;
reg buf10_ce0;
reg buf10_we0;
reg buf10_ce1;
reg buf11_ce0;
reg buf11_we0;
reg buf11_ce1;
reg buf12_ce0;
reg buf12_we0;
reg buf12_ce1;
reg buf13_ce0;
reg buf13_we0;
reg buf13_ce1;
reg buf14_ce0;
reg buf14_we0;
reg buf14_ce1;
reg buf15_ce0;
reg buf15_we0;
reg buf15_ce1;

(* fsm_encoding = "none" *) reg   [2:0] ap_CS_fsm;
wire    ap_CS_fsm_state1;
reg   [9:0] indvar_flatten_reg_360;
reg   [4:0] j_reg_371;
reg   [5:0] k_reg_382;
wire   [9:0] add_ln453_1_fu_393_p2;
wire    ap_CS_fsm_pp0_stage0;
reg    ap_enable_reg_pp0_iter0;
wire    ap_block_state2_pp0_stage0_iter0;
wire    ap_block_state3_pp0_stage0_iter1;
wire    ap_block_state4_pp0_stage0_iter2;
wire    ap_block_state5_pp0_stage0_iter3;
wire    ap_block_state6_pp0_stage0_iter4;
wire    ap_block_pp0_stage0_11001;
wire   [0:0] icmp_ln453_fu_399_p2;
reg   [0:0] icmp_ln453_reg_607;
reg   [0:0] icmp_ln453_reg_607_pp0_iter1_reg;
reg   [0:0] icmp_ln453_reg_607_pp0_iter2_reg;
wire   [5:0] select_ln453_fu_417_p3;
reg   [5:0] select_ln453_reg_611;
reg   [5:0] select_ln453_reg_611_pp0_iter1_reg;
wire   [4:0] select_ln453_1_fu_425_p3;
reg   [4:0] select_ln453_1_reg_616;
wire   [5:0] add_ln454_fu_437_p2;
reg   [9:0] buf_addr_reg_636;
reg   [9:0] buf1_addr_reg_642;
reg   [9:0] buf2_addr_reg_648;
reg   [9:0] buf3_addr_reg_654;
reg   [9:0] buf4_addr_reg_660;
reg   [9:0] buf5_addr_reg_666;
reg   [9:0] buf6_addr_reg_672;
reg   [9:0] buf7_addr_reg_678;
reg   [9:0] buf8_addr_reg_684;
reg   [9:0] buf9_addr_reg_690;
reg   [9:0] buf10_addr_reg_696;
reg   [9:0] buf11_addr_reg_702;
reg   [9:0] buf12_addr_reg_708;
reg   [9:0] buf13_addr_reg_714;
reg   [9:0] buf14_addr_reg_720;
reg   [9:0] buf15_addr_reg_726;
wire    ap_block_pp0_stage0_subdone;
reg    ap_condition_pp0_exit_iter0_state2;
reg    ap_enable_reg_pp0_iter1;
reg    ap_enable_reg_pp0_iter2;
reg    ap_enable_reg_pp0_iter3;
reg    ap_enable_reg_pp0_iter4;
reg   [4:0] ap_phi_mux_j_phi_fu_375_p4;
wire    ap_block_pp0_stage0;
wire   [63:0] zext_ln1495_1_fu_446_p1;
wire   [0:0] tmp_fu_465_p3;
wire   [0:0] tmp_91_fu_473_p3;
wire   [0:0] tmp_92_fu_481_p3;
wire   [0:0] tmp_93_fu_489_p3;
wire   [0:0] tmp_94_fu_497_p3;
wire   [0:0] tmp_95_fu_505_p3;
wire   [0:0] tmp_96_fu_513_p3;
wire   [0:0] tmp_97_fu_521_p3;
wire   [0:0] tmp_98_fu_529_p3;
wire   [0:0] tmp_99_fu_537_p3;
wire   [0:0] tmp_100_fu_545_p3;
wire   [0:0] tmp_101_fu_553_p3;
wire   [0:0] tmp_102_fu_561_p3;
wire   [0:0] tmp_103_fu_569_p3;
wire   [0:0] tmp_104_fu_577_p3;
wire   [0:0] tmp_105_fu_585_p3;
wire   [0:0] icmp_ln454_fu_411_p2;
wire   [4:0] add_ln453_fu_405_p2;
wire   [9:0] grp_fu_593_p3;
wire   [4:0] grp_fu_593_p0;
wire   [6:0] grp_fu_593_p1;
wire   [5:0] grp_fu_593_p2;
wire    ap_CS_fsm_state7;
reg   [2:0] ap_NS_fsm;
reg    ap_idle_pp0;
wire    ap_enable_pp0;
wire   [9:0] grp_fu_593_p00;
wire   [9:0] grp_fu_593_p20;
wire    ap_ce_reg;

// power-on initialization
initial begin
#0 ap_CS_fsm = 3'd1;
#0 ap_enable_reg_pp0_iter0 = 1'b0;
#0 ap_enable_reg_pp0_iter1 = 1'b0;
#0 ap_enable_reg_pp0_iter2 = 1'b0;
#0 ap_enable_reg_pp0_iter3 = 1'b0;
#0 ap_enable_reg_pp0_iter4 = 1'b0;
end

mobilenet_mac_muladd_5ns_7ns_6ns_10_4_1 #(
    .ID( 1 ),
    .NUM_STAGE( 4 ),
    .din0_WIDTH( 5 ),
    .din1_WIDTH( 7 ),
    .din2_WIDTH( 6 ),
    .dout_WIDTH( 10 ))
mac_muladd_5ns_7ns_6ns_10_4_1_U343(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(grp_fu_593_p0),
    .din1(grp_fu_593_p1),
    .din2(grp_fu_593_p2),
    .ce(1'b1),
    .dout(grp_fu_593_p3)
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
        ap_enable_reg_pp0_iter0 <= 1'b0;
    end else begin
        if (((1'b0 == ap_block_pp0_stage0_subdone) & (1'b1 == ap_condition_pp0_exit_iter0_state2) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
            ap_enable_reg_pp0_iter0 <= 1'b0;
        end else if (((ap_start == 1'b1) & (1'b1 == ap_CS_fsm_state1))) begin
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
        end else if (((ap_start == 1'b1) & (1'b1 == ap_CS_fsm_state1))) begin
            ap_enable_reg_pp0_iter4 <= 1'b0;
        end
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln453_fu_399_p2 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0) & (ap_enable_reg_pp0_iter0 == 1'b1))) begin
        indvar_flatten_reg_360 <= add_ln453_1_fu_393_p2;
    end else if (((ap_start == 1'b1) & (1'b1 == ap_CS_fsm_state1))) begin
        indvar_flatten_reg_360 <= 10'd0;
    end
end

always @ (posedge ap_clk) begin
    if (((ap_enable_reg_pp0_iter1 == 1'b1) & (icmp_ln453_reg_607 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        j_reg_371 <= select_ln453_1_reg_616;
    end else if (((ap_start == 1'b1) & (1'b1 == ap_CS_fsm_state1))) begin
        j_reg_371 <= 5'd1;
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln453_fu_399_p2 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0) & (ap_enable_reg_pp0_iter0 == 1'b1))) begin
        k_reg_382 <= add_ln454_fu_437_p2;
    end else if (((ap_start == 1'b1) & (1'b1 == ap_CS_fsm_state1))) begin
        k_reg_382 <= 6'd1;
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln453_reg_607_pp0_iter2_reg == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf10_addr_reg_696 <= zext_ln1495_1_fu_446_p1;
        buf11_addr_reg_702 <= zext_ln1495_1_fu_446_p1;
        buf12_addr_reg_708 <= zext_ln1495_1_fu_446_p1;
        buf13_addr_reg_714 <= zext_ln1495_1_fu_446_p1;
        buf14_addr_reg_720 <= zext_ln1495_1_fu_446_p1;
        buf15_addr_reg_726 <= zext_ln1495_1_fu_446_p1;
        buf1_addr_reg_642 <= zext_ln1495_1_fu_446_p1;
        buf2_addr_reg_648 <= zext_ln1495_1_fu_446_p1;
        buf3_addr_reg_654 <= zext_ln1495_1_fu_446_p1;
        buf4_addr_reg_660 <= zext_ln1495_1_fu_446_p1;
        buf5_addr_reg_666 <= zext_ln1495_1_fu_446_p1;
        buf6_addr_reg_672 <= zext_ln1495_1_fu_446_p1;
        buf7_addr_reg_678 <= zext_ln1495_1_fu_446_p1;
        buf8_addr_reg_684 <= zext_ln1495_1_fu_446_p1;
        buf9_addr_reg_690 <= zext_ln1495_1_fu_446_p1;
        buf_addr_reg_636 <= zext_ln1495_1_fu_446_p1;
    end
end

always @ (posedge ap_clk) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        icmp_ln453_reg_607 <= icmp_ln453_fu_399_p2;
        icmp_ln453_reg_607_pp0_iter1_reg <= icmp_ln453_reg_607;
        select_ln453_reg_611_pp0_iter1_reg <= select_ln453_reg_611;
    end
end

always @ (posedge ap_clk) begin
    if ((1'b0 == ap_block_pp0_stage0_11001)) begin
        icmp_ln453_reg_607_pp0_iter2_reg <= icmp_ln453_reg_607_pp0_iter1_reg;
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln453_fu_399_p2 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0) & (ap_enable_reg_pp0_iter0 == 1'b1))) begin
        select_ln453_1_reg_616 <= select_ln453_1_fu_425_p3;
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln453_fu_399_p2 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        select_ln453_reg_611 <= select_ln453_fu_417_p3;
    end
end

always @ (*) begin
    if ((icmp_ln453_fu_399_p2 == 1'd1)) begin
        ap_condition_pp0_exit_iter0_state2 = 1'b1;
    end else begin
        ap_condition_pp0_exit_iter0_state2 = 1'b0;
    end
end

always @ (*) begin
    if (((1'b1 == ap_CS_fsm_state7) | ((ap_start == 1'b0) & (1'b1 == ap_CS_fsm_state1)))) begin
        ap_done = 1'b1;
    end else begin
        ap_done = 1'b0;
    end
end

always @ (*) begin
    if (((ap_start == 1'b0) & (1'b1 == ap_CS_fsm_state1))) begin
        ap_idle = 1'b1;
    end else begin
        ap_idle = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b0) & (ap_enable_reg_pp0_iter3 == 1'b0) & (ap_enable_reg_pp0_iter2 == 1'b0) & (ap_enable_reg_pp0_iter1 == 1'b0) & (ap_enable_reg_pp0_iter0 == 1'b0))) begin
        ap_idle_pp0 = 1'b1;
    end else begin
        ap_idle_pp0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter1 == 1'b1) & (icmp_ln453_reg_607 == 1'd0) & (1'b0 == ap_block_pp0_stage0) & (1'b1 == ap_CS_fsm_pp0_stage0))) begin
        ap_phi_mux_j_phi_fu_375_p4 = select_ln453_1_reg_616;
    end else begin
        ap_phi_mux_j_phi_fu_375_p4 = j_reg_371;
    end
end

always @ (*) begin
    if ((1'b1 == ap_CS_fsm_state7)) begin
        ap_ready = 1'b1;
    end else begin
        ap_ready = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf10_ce0 = 1'b1;
    end else begin
        buf10_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf10_ce1 = 1'b1;
    end else begin
        buf10_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_100_fu_545_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf10_we0 = 1'b1;
    end else begin
        buf10_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf11_ce0 = 1'b1;
    end else begin
        buf11_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf11_ce1 = 1'b1;
    end else begin
        buf11_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_101_fu_553_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf11_we0 = 1'b1;
    end else begin
        buf11_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf12_ce0 = 1'b1;
    end else begin
        buf12_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf12_ce1 = 1'b1;
    end else begin
        buf12_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_102_fu_561_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf12_we0 = 1'b1;
    end else begin
        buf12_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf13_ce0 = 1'b1;
    end else begin
        buf13_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf13_ce1 = 1'b1;
    end else begin
        buf13_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_103_fu_569_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf13_we0 = 1'b1;
    end else begin
        buf13_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf14_ce0 = 1'b1;
    end else begin
        buf14_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf14_ce1 = 1'b1;
    end else begin
        buf14_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_104_fu_577_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf14_we0 = 1'b1;
    end else begin
        buf14_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf15_ce0 = 1'b1;
    end else begin
        buf15_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf15_ce1 = 1'b1;
    end else begin
        buf15_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_105_fu_585_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf15_we0 = 1'b1;
    end else begin
        buf15_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf1_ce0 = 1'b1;
    end else begin
        buf1_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf1_ce1 = 1'b1;
    end else begin
        buf1_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_91_fu_473_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf1_we0 = 1'b1;
    end else begin
        buf1_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf2_ce0 = 1'b1;
    end else begin
        buf2_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf2_ce1 = 1'b1;
    end else begin
        buf2_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_92_fu_481_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf2_we0 = 1'b1;
    end else begin
        buf2_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf3_ce0 = 1'b1;
    end else begin
        buf3_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf3_ce1 = 1'b1;
    end else begin
        buf3_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_93_fu_489_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf3_we0 = 1'b1;
    end else begin
        buf3_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf4_ce0 = 1'b1;
    end else begin
        buf4_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf4_ce1 = 1'b1;
    end else begin
        buf4_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_94_fu_497_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf4_we0 = 1'b1;
    end else begin
        buf4_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf5_ce0 = 1'b1;
    end else begin
        buf5_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf5_ce1 = 1'b1;
    end else begin
        buf5_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_95_fu_505_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf5_we0 = 1'b1;
    end else begin
        buf5_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf6_ce0 = 1'b1;
    end else begin
        buf6_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf6_ce1 = 1'b1;
    end else begin
        buf6_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_96_fu_513_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf6_we0 = 1'b1;
    end else begin
        buf6_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf7_ce0 = 1'b1;
    end else begin
        buf7_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf7_ce1 = 1'b1;
    end else begin
        buf7_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_97_fu_521_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf7_we0 = 1'b1;
    end else begin
        buf7_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf8_ce0 = 1'b1;
    end else begin
        buf8_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf8_ce1 = 1'b1;
    end else begin
        buf8_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_98_fu_529_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf8_we0 = 1'b1;
    end else begin
        buf8_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf9_ce0 = 1'b1;
    end else begin
        buf9_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf9_ce1 = 1'b1;
    end else begin
        buf9_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_99_fu_537_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf9_we0 = 1'b1;
    end else begin
        buf9_we0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf_r_ce0 = 1'b1;
    end else begin
        buf_r_ce0 = 1'b0;
    end
end

always @ (*) begin
    if (((ap_enable_reg_pp0_iter3 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf_r_ce1 = 1'b1;
    end else begin
        buf_r_ce1 = 1'b0;
    end
end

always @ (*) begin
    if (((tmp_fu_465_p3 == 1'd1) & (ap_enable_reg_pp0_iter4 == 1'b1) & (1'b0 == ap_block_pp0_stage0_11001))) begin
        buf_r_we0 = 1'b1;
    end else begin
        buf_r_we0 = 1'b0;
    end
end

always @ (*) begin
    case (ap_CS_fsm)
        ap_ST_fsm_state1 : begin
            if (((ap_start == 1'b1) & (1'b1 == ap_CS_fsm_state1))) begin
                ap_NS_fsm = ap_ST_fsm_pp0_stage0;
            end else begin
                ap_NS_fsm = ap_ST_fsm_state1;
            end
        end
        ap_ST_fsm_pp0_stage0 : begin
            if ((~((ap_enable_reg_pp0_iter1 == 1'b0) & (icmp_ln453_fu_399_p2 == 1'd1) & (1'b0 == ap_block_pp0_stage0_subdone) & (ap_enable_reg_pp0_iter0 == 1'b1)) & ~((ap_enable_reg_pp0_iter4 == 1'b1) & (ap_enable_reg_pp0_iter3 == 1'b0) & (1'b0 == ap_block_pp0_stage0_subdone)))) begin
                ap_NS_fsm = ap_ST_fsm_pp0_stage0;
            end else if ((((ap_enable_reg_pp0_iter4 == 1'b1) & (ap_enable_reg_pp0_iter3 == 1'b0) & (1'b0 == ap_block_pp0_stage0_subdone)) | ((ap_enable_reg_pp0_iter1 == 1'b0) & (icmp_ln453_fu_399_p2 == 1'd1) & (1'b0 == ap_block_pp0_stage0_subdone) & (ap_enable_reg_pp0_iter0 == 1'b1)))) begin
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

assign add_ln453_1_fu_393_p2 = (indvar_flatten_reg_360 + 10'd1);

assign add_ln453_fu_405_p2 = (ap_phi_mux_j_phi_fu_375_p4 + 5'd1);

assign add_ln454_fu_437_p2 = (select_ln453_fu_417_p3 + 6'd1);

assign ap_CS_fsm_pp0_stage0 = ap_CS_fsm[32'd1];

assign ap_CS_fsm_state1 = ap_CS_fsm[32'd0];

assign ap_CS_fsm_state7 = ap_CS_fsm[32'd2];

assign ap_block_pp0_stage0 = ~(1'b1 == 1'b1);

assign ap_block_pp0_stage0_11001 = ~(1'b1 == 1'b1);

assign ap_block_pp0_stage0_subdone = ~(1'b1 == 1'b1);

assign ap_block_state2_pp0_stage0_iter0 = ~(1'b1 == 1'b1);

assign ap_block_state3_pp0_stage0_iter1 = ~(1'b1 == 1'b1);

assign ap_block_state4_pp0_stage0_iter2 = ~(1'b1 == 1'b1);

assign ap_block_state5_pp0_stage0_iter3 = ~(1'b1 == 1'b1);

assign ap_block_state6_pp0_stage0_iter4 = ~(1'b1 == 1'b1);

assign ap_enable_pp0 = (ap_idle_pp0 ^ 1'b1);

assign buf10_address0 = buf10_addr_reg_696;

assign buf10_address1 = zext_ln1495_1_fu_446_p1;

assign buf10_d0 = 16'd0;

assign buf11_address0 = buf11_addr_reg_702;

assign buf11_address1 = zext_ln1495_1_fu_446_p1;

assign buf11_d0 = 16'd0;

assign buf12_address0 = buf12_addr_reg_708;

assign buf12_address1 = zext_ln1495_1_fu_446_p1;

assign buf12_d0 = 16'd0;

assign buf13_address0 = buf13_addr_reg_714;

assign buf13_address1 = zext_ln1495_1_fu_446_p1;

assign buf13_d0 = 16'd0;

assign buf14_address0 = buf14_addr_reg_720;

assign buf14_address1 = zext_ln1495_1_fu_446_p1;

assign buf14_d0 = 16'd0;

assign buf15_address0 = buf15_addr_reg_726;

assign buf15_address1 = zext_ln1495_1_fu_446_p1;

assign buf15_d0 = 16'd0;

assign buf1_address0 = buf1_addr_reg_642;

assign buf1_address1 = zext_ln1495_1_fu_446_p1;

assign buf1_d0 = 16'd0;

assign buf2_address0 = buf2_addr_reg_648;

assign buf2_address1 = zext_ln1495_1_fu_446_p1;

assign buf2_d0 = 16'd0;

assign buf3_address0 = buf3_addr_reg_654;

assign buf3_address1 = zext_ln1495_1_fu_446_p1;

assign buf3_d0 = 16'd0;

assign buf4_address0 = buf4_addr_reg_660;

assign buf4_address1 = zext_ln1495_1_fu_446_p1;

assign buf4_d0 = 16'd0;

assign buf5_address0 = buf5_addr_reg_666;

assign buf5_address1 = zext_ln1495_1_fu_446_p1;

assign buf5_d0 = 16'd0;

assign buf6_address0 = buf6_addr_reg_672;

assign buf6_address1 = zext_ln1495_1_fu_446_p1;

assign buf6_d0 = 16'd0;

assign buf7_address0 = buf7_addr_reg_678;

assign buf7_address1 = zext_ln1495_1_fu_446_p1;

assign buf7_d0 = 16'd0;

assign buf8_address0 = buf8_addr_reg_684;

assign buf8_address1 = zext_ln1495_1_fu_446_p1;

assign buf8_d0 = 16'd0;

assign buf9_address0 = buf9_addr_reg_690;

assign buf9_address1 = zext_ln1495_1_fu_446_p1;

assign buf9_d0 = 16'd0;

assign buf_r_address0 = buf_addr_reg_636;

assign buf_r_address1 = zext_ln1495_1_fu_446_p1;

assign buf_r_d0 = 16'd0;

assign grp_fu_593_p0 = grp_fu_593_p00;

assign grp_fu_593_p00 = select_ln453_1_fu_425_p3;

assign grp_fu_593_p1 = 10'd42;

assign grp_fu_593_p2 = grp_fu_593_p20;

assign grp_fu_593_p20 = select_ln453_reg_611_pp0_iter1_reg;

assign icmp_ln453_fu_399_p2 = ((indvar_flatten_reg_360 == 10'd800) ? 1'b1 : 1'b0);

assign icmp_ln454_fu_411_p2 = ((k_reg_382 == 6'd41) ? 1'b1 : 1'b0);

assign select_ln453_1_fu_425_p3 = ((icmp_ln454_fu_411_p2[0:0] == 1'b1) ? add_ln453_fu_405_p2 : ap_phi_mux_j_phi_fu_375_p4);

assign select_ln453_fu_417_p3 = ((icmp_ln454_fu_411_p2[0:0] == 1'b1) ? 6'd1 : k_reg_382);

assign tmp_100_fu_545_p3 = buf10_q1[32'd15];

assign tmp_101_fu_553_p3 = buf11_q1[32'd15];

assign tmp_102_fu_561_p3 = buf12_q1[32'd15];

assign tmp_103_fu_569_p3 = buf13_q1[32'd15];

assign tmp_104_fu_577_p3 = buf14_q1[32'd15];

assign tmp_105_fu_585_p3 = buf15_q1[32'd15];

assign tmp_91_fu_473_p3 = buf1_q1[32'd15];

assign tmp_92_fu_481_p3 = buf2_q1[32'd15];

assign tmp_93_fu_489_p3 = buf3_q1[32'd15];

assign tmp_94_fu_497_p3 = buf4_q1[32'd15];

assign tmp_95_fu_505_p3 = buf5_q1[32'd15];

assign tmp_96_fu_513_p3 = buf6_q1[32'd15];

assign tmp_97_fu_521_p3 = buf7_q1[32'd15];

assign tmp_98_fu_529_p3 = buf8_q1[32'd15];

assign tmp_99_fu_537_p3 = buf9_q1[32'd15];

assign tmp_fu_465_p3 = buf_r_q1[32'd15];

assign zext_ln1495_1_fu_446_p1 = grp_fu_593_p3;

endmodule //mobilenet_Relu