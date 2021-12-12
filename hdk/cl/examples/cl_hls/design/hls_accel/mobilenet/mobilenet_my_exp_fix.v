// ==============================================================
// RTL generated by Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
// Version: 2020.2
// Copyright (C) Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
// 
// ===========================================================

`timescale 1 ns / 1 ps 

module mobilenet_my_exp_fix (
        ap_clk,
        ap_rst,
        input_r,
        ap_return,
        ap_ce
);


input   ap_clk;
input   ap_rst;
input  [15:0] input_r;
output  [31:0] ap_return;
input   ap_ce;

reg[31:0] ap_return;

wire   [0:0] icmp_ln935_fu_160_p2;
reg   [0:0] icmp_ln935_reg_1289;
wire    ap_block_state1_pp0_stage0_iter0;
wire    ap_block_state2_pp0_stage0_iter1;
wire    ap_block_state3_pp0_stage0_iter2;
wire    ap_block_state4_pp0_stage0_iter3;
wire    ap_block_state5_pp0_stage0_iter4;
wire    ap_block_state6_pp0_stage0_iter5;
wire    ap_block_state7_pp0_stage0_iter6;
wire    ap_block_state8_pp0_stage0_iter7;
wire    ap_block_state9_pp0_stage0_iter8;
wire    ap_block_state10_pp0_stage0_iter9;
wire    ap_block_state11_pp0_stage0_iter10;
wire    ap_block_state12_pp0_stage0_iter11;
wire    ap_block_state13_pp0_stage0_iter12;
wire    ap_block_state14_pp0_stage0_iter13;
wire    ap_block_state15_pp0_stage0_iter14;
wire    ap_block_state16_pp0_stage0_iter15;
wire    ap_block_state17_pp0_stage0_iter16;
wire    ap_block_state18_pp0_stage0_iter17;
wire    ap_block_pp0_stage0_11001;
reg   [0:0] icmp_ln935_reg_1289_pp0_iter1_reg;
wire   [0:0] p_Result_13_fu_166_p3;
reg   [0:0] p_Result_13_reg_1294;
reg   [0:0] p_Result_13_reg_1294_pp0_iter1_reg;
wire   [15:0] m_5_fu_180_p3;
reg   [15:0] m_5_reg_1299;
reg   [15:0] m_5_reg_1299_pp0_iter1_reg;
reg   [15:0] p_Result_s_fu_188_p4;
reg   [15:0] p_Result_s_reg_1306;
wire   [0:0] icmp_ln958_fu_315_p2;
reg   [0:0] icmp_ln958_reg_1311;
wire   [31:0] sub_ln959_fu_321_p2;
reg   [31:0] sub_ln959_reg_1316;
wire   [31:0] add_ln958_fu_327_p2;
reg   [31:0] add_ln958_reg_1321;
wire   [0:0] tobool34_i_i11_fu_333_p2;
reg   [0:0] tobool34_i_i11_reg_1326;
wire   [7:0] trunc_ln943_fu_339_p1;
reg   [7:0] trunc_ln943_reg_1331;
wire   [31:0] select_ln935_fu_448_p3;
reg   [31:0] select_ln935_reg_1336;
wire   [31:0] grp_fu_155_p2;
reg   [31:0] v_assign_reg_1341;
reg   [31:0] v_assign_reg_1341_pp0_iter13_reg;
reg   [31:0] v_assign_reg_1341_pp0_iter14_reg;
reg   [0:0] p_Result_16_reg_1347;
reg   [0:0] p_Result_16_reg_1347_pp0_iter15_reg;
wire   [11:0] zext_ln455_fu_481_p1;
reg   [11:0] zext_ln455_reg_1357;
wire   [53:0] zext_ln569_fu_497_p1;
reg   [53:0] zext_ln569_reg_1362;
wire   [53:0] man_V_2_fu_501_p2;
reg   [53:0] man_V_2_reg_1367;
wire   [0:0] icmp_ln571_fu_507_p2;
reg   [0:0] icmp_ln571_reg_1372;
reg   [0:0] icmp_ln571_reg_1372_pp0_iter15_reg;
reg   [0:0] icmp_ln571_reg_1372_pp0_iter16_reg;
wire   [11:0] F2_fu_513_p2;
reg   [11:0] F2_reg_1379;
reg   [11:0] F2_reg_1379_pp0_iter15_reg;
wire   [10:0] trunc_ln575_fu_519_p1;
reg   [10:0] trunc_ln575_reg_1391;
wire   [0:0] QUAN_INC_fu_533_p2;
reg   [0:0] QUAN_INC_reg_1396;
reg   [0:0] QUAN_INC_reg_1396_pp0_iter15_reg;
wire   [5:0] trunc_ln595_fu_539_p1;
reg   [5:0] trunc_ln595_reg_1403;
wire   [5:0] trunc_ln619_fu_543_p1;
reg   [5:0] trunc_ln619_reg_1408;
wire  signed [11:0] sh_amt_fu_562_p3;
reg  signed [11:0] sh_amt_reg_1413;
wire   [31:0] trunc_ln583_fu_569_p1;
reg   [31:0] trunc_ln583_reg_1418;
wire   [0:0] icmp_ln603_fu_589_p2;
reg   [0:0] icmp_ln603_reg_1424;
wire   [31:0] p_Val2_4_fu_632_p3;
reg   [31:0] p_Val2_4_reg_1430;
wire   [0:0] icmp_ln595_1_fu_715_p2;
reg   [0:0] icmp_ln595_1_reg_1435;
wire   [0:0] or_ln594_fu_721_p2;
reg   [0:0] or_ln594_reg_1440;
wire   [0:0] select_ln594_fu_727_p3;
reg   [0:0] select_ln594_reg_1445;
reg   [0:0] p_Result_19_reg_1450;
wire   [0:0] icmp_ln611_fu_759_p2;
reg   [0:0] icmp_ln611_reg_1456;
reg   [0:0] icmp_ln611_reg_1456_pp0_iter16_reg;
wire  signed [11:0] pos1_fu_765_p2;
reg  signed [11:0] pos1_reg_1462;
reg   [0:0] tmp_12_reg_1469;
wire   [0:0] lD_fu_782_p3;
reg   [0:0] lD_reg_1474;
wire   [0:0] Range2_all_ones_fu_811_p2;
reg   [0:0] Range2_all_ones_reg_1479;
wire   [0:0] icmp_ln641_fu_817_p2;
reg   [0:0] icmp_ln641_reg_1484;
wire   [31:0] p_Val2_6_fu_927_p3;
reg   [31:0] p_Val2_6_reg_1489;
wire   [0:0] neg_src_1_fu_1160_p3;
reg   [0:0] neg_src_1_reg_1496;
wire   [0:0] overflow_fu_1191_p2;
reg   [0:0] overflow_reg_1502;
wire   [0:0] and_ln659_fu_1197_p2;
reg   [0:0] and_ln659_reg_1508;
wire    ap_block_pp0_stage0;
wire   [15:0] tmp_V_fu_174_p2;
wire   [31:0] p_Result_14_fu_198_p3;
reg   [31:0] l_fu_205_p3;
wire   [31:0] sub_ln944_fu_213_p2;
wire   [31:0] lsb_index_fu_223_p2;
wire   [30:0] tmp_2_fu_229_p4;
wire   [4:0] trunc_ln947_fu_245_p1;
wire   [4:0] sub_ln947_fu_249_p2;
wire   [15:0] zext_ln947_fu_255_p1;
wire   [15:0] lshr_ln947_fu_259_p2;
wire   [15:0] p_Result_4_fu_265_p2;
wire   [0:0] tmp_3_fu_276_p3;
wire   [0:0] icmp_ln946_fu_239_p2;
wire   [0:0] icmp_ln947_fu_270_p2;
wire   [15:0] trunc_ln944_fu_219_p1;
wire   [15:0] add_ln949_fu_296_p2;
wire   [0:0] p_Result_3_fu_302_p3;
wire   [0:0] and_ln946_fu_290_p2;
wire   [0:0] a_fu_309_p2;
wire   [0:0] xor_ln949_fu_284_p2;
wire   [63:0] zext_ln957_fu_343_p1;
wire   [63:0] zext_ln959_fu_346_p1;
wire   [63:0] zext_ln958_fu_355_p1;
wire   [63:0] lshr_ln958_fu_358_p2;
wire   [63:0] shl_ln959_fu_349_p2;
wire   [63:0] m_fu_364_p3;
wire   [63:0] zext_ln961_fu_371_p1;
wire   [63:0] m_2_fu_374_p2;
wire   [62:0] m_6_fu_380_p4;
wire   [0:0] p_Result_5_fu_394_p3;
wire   [7:0] sub_ln964_fu_410_p2;
wire   [7:0] select_ln943_fu_402_p3;
wire   [7:0] add_ln964_fu_415_p2;
wire   [63:0] zext_ln962_fu_390_p1;
wire   [8:0] tmp_fu_421_p3;
wire   [63:0] p_Result_15_fu_428_p5;
wire   [31:0] LD_fu_440_p1;
wire   [31:0] bitcast_ln744_fu_444_p1;
wire   [63:0] grp_fu_152_p1;
wire   [63:0] ireg_fu_455_p1;
wire   [10:0] exp_tmp_fu_471_p4;
wire   [51:0] trunc_ln565_fu_485_p1;
wire   [52:0] p_Result_17_fu_489_p3;
wire   [62:0] trunc_ln555_fu_459_p1;
wire   [8:0] tmp_6_fu_523_p4;
wire   [11:0] add_ln581_fu_552_p2;
wire   [11:0] sub_ln581_fu_557_p2;
wire   [53:0] man_V_fu_547_p3;
wire   [6:0] tmp_7_fu_579_p4;
wire   [5:0] trunc_ln586_fu_595_p1;
wire   [53:0] zext_ln586_fu_599_p1;
wire   [53:0] ashr_ln586_fu_603_p2;
wire   [31:0] bitcast_ln702_fu_613_p1;
wire   [0:0] tmp_8_fu_616_p3;
wire   [0:0] icmp_ln585_fu_573_p2;
wire   [31:0] trunc_ln586_1_fu_609_p1;
wire   [31:0] select_ln588_fu_624_p3;
wire   [10:0] add_ln591_fu_646_p2;
wire   [31:0] zext_ln591_fu_651_p1;
wire   [0:0] icmp_ln591_fu_640_p2;
wire   [0:0] p_Result_18_fu_655_p3;
wire   [11:0] add_ln595_fu_675_p2;
wire   [0:0] icmp_ln595_fu_680_p2;
wire   [5:0] sub_ln595_fu_686_p2;
wire   [5:0] select_ln595_fu_691_p3;
wire   [53:0] zext_ln595_fu_699_p1;
wire   [53:0] lshr_ln595_fu_703_p2;
wire   [53:0] p_Result_10_fu_709_p2;
wire   [0:0] icmp_ln594_fu_663_p2;
wire   [0:0] select_ln591_fu_668_p3;
wire   [10:0] or_ln_fu_743_p3;
wire  signed [11:0] sext_ln612_fu_750_p1;
wire   [11:0] add_ln612_fu_754_p2;
wire  signed [31:0] sext_ln618_fu_770_p1;
wire   [5:0] add_ln635_fu_790_p2;
wire   [53:0] zext_ln635_fu_795_p1;
wire   [53:0] Range2_V_1_fu_799_p2;
wire   [53:0] r_fu_805_p2;
wire  signed [31:0] sext_ln581_fu_823_p1;
wire   [0:0] r_1_fu_836_p2;
wire   [0:0] or_ln414_fu_840_p2;
wire   [0:0] and_ln414_fu_845_p2;
wire   [31:0] zext_ln415_fu_850_p1;
wire   [31:0] p_Val2_5_fu_854_p2;
wire   [0:0] icmp_ln582_fu_826_p2;
wire   [0:0] xor_ln582_fu_874_p2;
wire   [0:0] and_ln577_fu_880_p2;
wire   [0:0] and_ln403_fu_885_p2;
wire   [31:0] select_ln582_fu_867_p3;
wire   [0:0] xor_ln403_fu_898_p2;
wire   [0:0] and_ln403_1_fu_903_p2;
wire   [31:0] select_ln403_fu_890_p3;
wire   [0:0] icmp_ln577_fu_917_p2;
wire   [0:0] and_ln603_fu_922_p2;
wire   [31:0] shl_ln604_fu_831_p2;
wire   [31:0] select_ln403_1_fu_909_p3;
wire   [0:0] tmp_10_fu_859_p3;
wire   [0:0] and_ln603_1_fu_935_p2;
wire   [0:0] or_ln603_fu_940_p2;
wire   [0:0] xor_ln603_fu_946_p2;
wire   [0:0] icmp_ln621_1_fu_981_p2;
wire   [11:0] pos2_fu_958_p2;
wire   [0:0] tmp_13_fu_1003_p3;
wire   [0:0] icmp_ln631_1_fu_997_p2;
wire   [0:0] Range2_all_ones_1_fu_1011_p2;
wire   [0:0] icmp_ln631_fu_991_p2;
wire   [0:0] xor_ln621_1_fu_976_p2;
wire   [0:0] Range2_all_ones_2_fu_1017_p3;
wire   [0:0] Range1_all_ones_3_fu_986_p2;
wire   [0:0] Range1_all_zeros_fu_1036_p2;
wire   [0:0] icmp_ln642_fu_1047_p2;
wire   [0:0] and_ln639_fu_1024_p2;
wire   [0:0] Range1_all_ones_fu_1030_p2;
wire   [0:0] select_ln642_fu_1053_p3;
wire   [0:0] and_ln641_fu_1042_p2;
wire   [0:0] select_ln642_1_fu_1061_p3;
wire   [0:0] carry_1_fu_952_p2;
wire   [0:0] Range1_all_ones_2_fu_1069_p3;
wire   [0:0] Range1_all_zeros_1_fu_1077_p3;
wire   [0:0] tmp_14_fu_1093_p3;
wire   [0:0] or_ln653_fu_1100_p2;
wire   [0:0] and_ln653_fu_1106_p2;
wire   [0:0] and_ln654_fu_1120_p2;
wire   [0:0] icmp_ln621_fu_971_p2;
wire   [0:0] deleted_ones_fu_1112_p3;
wire   [0:0] xor_ln621_fu_1132_p2;
wire   [0:0] p_Result_20_fu_963_p3;
wire   [0:0] and_ln621_fu_1144_p2;
wire   [0:0] and_ln557_fu_1155_p2;
wire   [0:0] xor_ln654_fu_1126_p2;
wire   [0:0] and_ln621_1_fu_1150_p2;
wire   [0:0] deleted_zeros_fu_1085_p3;
wire   [0:0] xor_ln658_fu_1168_p2;
wire   [0:0] and_ln658_fu_1174_p2;
wire   [0:0] or_ln658_fu_1180_p2;
wire   [0:0] xor_ln658_1_fu_1186_p2;
wire   [0:0] deleted_ones_1_fu_1138_p2;
wire   [0:0] xor_ln659_fu_1203_p2;
wire   [0:0] underflow_fu_1208_p2;
wire   [0:0] xor_ln340_fu_1218_p2;
wire   [0:0] or_ln340_2_fu_1223_p2;
wire   [0:0] or_ln340_fu_1213_p2;
wire   [0:0] or_ln340_1_fu_1228_p2;
wire   [0:0] xor_ln571_fu_1247_p2;
wire   [0:0] and_ln340_fu_1252_p2;
wire   [0:0] and_ln340_1_fu_1258_p2;
wire   [31:0] select_ln340_fu_1233_p3;
wire   [31:0] select_ln388_fu_1240_p3;
wire   [0:0] or_ln611_fu_1271_p2;
wire   [31:0] select_ln340_1_fu_1263_p3;
wire   [31:0] select_ln611_fu_1275_p3;
reg    grp_fu_152_ce;
reg    grp_fu_155_ce;
wire   [31:0] output_V_fu_1282_p3;
reg    ap_ce_reg;
reg   [15:0] input_r_int_reg;
reg   [31:0] ap_return_int_reg;

mobilenet_fpext_32ns_64_2_no_dsp_0 #(
    .ID( 1 ),
    .NUM_STAGE( 2 ),
    .din0_WIDTH( 32 ),
    .dout_WIDTH( 64 ))
fpext_32ns_64_2_no_dsp_0_U661(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(v_assign_reg_1341),
    .ce(grp_fu_152_ce),
    .dout(grp_fu_152_p1)
);

mobilenet_fexp_32ns_32ns_32_10_full_dsp_0 #(
    .ID( 1 ),
    .NUM_STAGE( 10 ),
    .din0_WIDTH( 32 ),
    .din1_WIDTH( 32 ),
    .dout_WIDTH( 32 ))
fexp_32ns_32ns_32_10_full_dsp_0_U662(
    .clk(ap_clk),
    .reset(ap_rst),
    .din0(32'd0),
    .din1(select_ln935_reg_1336),
    .ce(grp_fu_155_ce),
    .dout(grp_fu_155_p2)
);

always @ (posedge ap_clk) begin
    ap_ce_reg <= ap_ce;
end

always @ (posedge ap_clk) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_ce_reg))) begin
        F2_reg_1379 <= F2_fu_513_p2;
        F2_reg_1379_pp0_iter15_reg <= F2_reg_1379;
        QUAN_INC_reg_1396 <= QUAN_INC_fu_533_p2;
        QUAN_INC_reg_1396_pp0_iter15_reg <= QUAN_INC_reg_1396;
        icmp_ln571_reg_1372 <= icmp_ln571_fu_507_p2;
        icmp_ln571_reg_1372_pp0_iter15_reg <= icmp_ln571_reg_1372;
        icmp_ln571_reg_1372_pp0_iter16_reg <= icmp_ln571_reg_1372_pp0_iter15_reg;
        icmp_ln611_reg_1456_pp0_iter16_reg <= icmp_ln611_reg_1456;
        icmp_ln935_reg_1289 <= icmp_ln935_fu_160_p2;
        icmp_ln935_reg_1289_pp0_iter1_reg <= icmp_ln935_reg_1289;
        m_5_reg_1299 <= m_5_fu_180_p3;
        m_5_reg_1299_pp0_iter1_reg <= m_5_reg_1299;
        man_V_2_reg_1367 <= man_V_2_fu_501_p2;
        p_Result_13_reg_1294 <= input_r_int_reg[32'd15];
        p_Result_13_reg_1294_pp0_iter1_reg <= p_Result_13_reg_1294;
        p_Result_16_reg_1347 <= ireg_fu_455_p1[32'd63];
        p_Result_16_reg_1347_pp0_iter15_reg <= p_Result_16_reg_1347;
        p_Result_s_reg_1306 <= p_Result_s_fu_188_p4;
        select_ln935_reg_1336 <= select_ln935_fu_448_p3;
        trunc_ln575_reg_1391 <= trunc_ln575_fu_519_p1;
        trunc_ln595_reg_1403 <= trunc_ln595_fu_539_p1;
        trunc_ln619_reg_1408 <= trunc_ln619_fu_543_p1;
        v_assign_reg_1341 <= grp_fu_155_p2;
        v_assign_reg_1341_pp0_iter13_reg <= v_assign_reg_1341;
        v_assign_reg_1341_pp0_iter14_reg <= v_assign_reg_1341_pp0_iter13_reg;
        zext_ln455_reg_1357[10 : 0] <= zext_ln455_fu_481_p1[10 : 0];
        zext_ln569_reg_1362[51 : 0] <= zext_ln569_fu_497_p1[51 : 0];
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln571_reg_1372 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_ce_reg))) begin
        Range2_all_ones_reg_1479 <= Range2_all_ones_fu_811_p2;
        icmp_ln595_1_reg_1435 <= icmp_ln595_1_fu_715_p2;
        icmp_ln603_reg_1424 <= icmp_ln603_fu_589_p2;
        icmp_ln611_reg_1456 <= icmp_ln611_fu_759_p2;
        icmp_ln641_reg_1484 <= icmp_ln641_fu_817_p2;
        lD_reg_1474 <= lD_fu_782_p3;
        or_ln594_reg_1440 <= or_ln594_fu_721_p2;
        p_Result_19_reg_1450 <= p_Val2_4_fu_632_p3[32'd31];
        p_Val2_4_reg_1430 <= p_Val2_4_fu_632_p3;
        pos1_reg_1462 <= pos1_fu_765_p2;
        select_ln594_reg_1445 <= select_ln594_fu_727_p3;
        sh_amt_reg_1413 <= sh_amt_fu_562_p3;
        tmp_12_reg_1469 <= pos1_fu_765_p2[32'd11];
        trunc_ln583_reg_1418 <= trunc_ln583_fu_569_p1;
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln935_reg_1289 == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_ce_reg))) begin
        add_ln958_reg_1321 <= add_ln958_fu_327_p2;
        icmp_ln958_reg_1311 <= icmp_ln958_fu_315_p2;
        sub_ln959_reg_1316 <= sub_ln959_fu_321_p2;
        tobool34_i_i11_reg_1326 <= tobool34_i_i11_fu_333_p2;
        trunc_ln943_reg_1331 <= trunc_ln943_fu_339_p1;
    end
end

always @ (posedge ap_clk) begin
    if (((icmp_ln571_reg_1372_pp0_iter15_reg == 1'd0) & (1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_ce_reg))) begin
        and_ln659_reg_1508 <= and_ln659_fu_1197_p2;
        neg_src_1_reg_1496 <= neg_src_1_fu_1160_p3;
        overflow_reg_1502 <= overflow_fu_1191_p2;
        p_Val2_6_reg_1489 <= p_Val2_6_fu_927_p3;
    end
end

always @ (posedge ap_clk) begin
    if ((1'b1 == ap_ce_reg)) begin
        ap_return_int_reg <= output_V_fu_1282_p3;
    end
end

always @ (posedge ap_clk) begin
    if ((1'b1 == ap_ce)) begin
        input_r_int_reg <= input_r;
    end
end

always @ (*) begin
    if ((1'b0 == ap_ce_reg)) begin
        ap_return = ap_return_int_reg;
    end else if ((1'b1 == ap_ce_reg)) begin
        ap_return = output_V_fu_1282_p3;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_ce_reg))) begin
        grp_fu_152_ce = 1'b1;
    end else begin
        grp_fu_152_ce = 1'b0;
    end
end

always @ (*) begin
    if (((1'b0 == ap_block_pp0_stage0_11001) & (1'b1 == ap_ce_reg))) begin
        grp_fu_155_ce = 1'b1;
    end else begin
        grp_fu_155_ce = 1'b0;
    end
end

assign F2_fu_513_p2 = (12'd1075 - zext_ln455_fu_481_p1);

assign LD_fu_440_p1 = p_Result_15_fu_428_p5[31:0];

assign QUAN_INC_fu_533_p2 = (($signed(tmp_6_fu_523_p4) > $signed(9'd0)) ? 1'b1 : 1'b0);

assign Range1_all_ones_2_fu_1069_p3 = ((and_ln639_fu_1024_p2[0:0] == 1'b1) ? Range1_all_ones_fu_1030_p2 : select_ln642_fu_1053_p3);

assign Range1_all_ones_3_fu_986_p2 = (lD_reg_1474 & icmp_ln621_1_fu_981_p2);

assign Range1_all_ones_fu_1030_p2 = (Range2_all_ones_2_fu_1017_p3 & Range1_all_ones_3_fu_986_p2);

assign Range1_all_zeros_1_fu_1077_p3 = ((and_ln639_fu_1024_p2[0:0] == 1'b1) ? and_ln641_fu_1042_p2 : select_ln642_1_fu_1061_p3);

assign Range1_all_zeros_fu_1036_p2 = (1'd1 ^ Range1_all_ones_3_fu_986_p2);

assign Range2_V_1_fu_799_p2 = man_V_fu_547_p3 >> zext_ln635_fu_795_p1;

assign Range2_all_ones_1_fu_1011_p2 = (tmp_13_fu_1003_p3 ^ 1'd1);

assign Range2_all_ones_2_fu_1017_p3 = ((icmp_ln631_1_fu_997_p2[0:0] == 1'b1) ? Range2_all_ones_reg_1479 : Range2_all_ones_1_fu_1011_p2);

assign Range2_all_ones_fu_811_p2 = ((Range2_V_1_fu_799_p2 == r_fu_805_p2) ? 1'b1 : 1'b0);

assign a_fu_309_p2 = (p_Result_3_fu_302_p3 | and_ln946_fu_290_p2);

assign add_ln581_fu_552_p2 = ($signed(F2_reg_1379) + $signed(12'd4089));

assign add_ln591_fu_646_p2 = ($signed(trunc_ln575_reg_1391) + $signed(11'd2040));

assign add_ln595_fu_675_p2 = ($signed(F2_reg_1379) + $signed(12'd4087));

assign add_ln612_fu_754_p2 = ($signed(sext_ln612_fu_750_p1) + $signed(zext_ln455_reg_1357));

assign add_ln635_fu_790_p2 = (trunc_ln619_reg_1408 + 6'd26);

assign add_ln949_fu_296_p2 = ($signed(trunc_ln944_fu_219_p1) + $signed(16'd65512));

assign add_ln958_fu_327_p2 = ($signed(sub_ln944_fu_213_p2) + $signed(32'd4294967271));

assign add_ln964_fu_415_p2 = (sub_ln964_fu_410_p2 + select_ln943_fu_402_p3);

assign and_ln340_1_fu_1258_p2 = (icmp_ln611_reg_1456_pp0_iter16_reg & and_ln340_fu_1252_p2);

assign and_ln340_fu_1252_p2 = (xor_ln571_fu_1247_p2 & or_ln340_1_fu_1228_p2);

assign and_ln403_1_fu_903_p2 = (xor_ln403_fu_898_p2 & and_ln577_fu_880_p2);

assign and_ln403_fu_885_p2 = (p_Result_19_reg_1450 & and_ln577_fu_880_p2);

assign and_ln414_fu_845_p2 = (p_Result_16_reg_1347_pp0_iter15_reg & or_ln414_fu_840_p2);

assign and_ln557_fu_1155_p2 = (p_Result_16_reg_1347_pp0_iter15_reg & icmp_ln621_fu_971_p2);

assign and_ln577_fu_880_p2 = (xor_ln582_fu_874_p2 & QUAN_INC_reg_1396_pp0_iter15_reg);

assign and_ln603_1_fu_935_p2 = (icmp_ln603_reg_1424 & icmp_ln577_fu_917_p2);

assign and_ln603_fu_922_p2 = (icmp_ln603_reg_1424 & icmp_ln577_fu_917_p2);

assign and_ln621_1_fu_1150_p2 = (p_Result_16_reg_1347_pp0_iter15_reg & and_ln621_fu_1144_p2);

assign and_ln621_fu_1144_p2 = (xor_ln621_fu_1132_p2 & p_Result_20_fu_963_p3);

assign and_ln639_fu_1024_p2 = (xor_ln621_1_fu_976_p2 & icmp_ln631_fu_991_p2);

assign and_ln641_fu_1042_p2 = (icmp_ln641_reg_1484 & Range1_all_zeros_fu_1036_p2);

assign and_ln653_fu_1106_p2 = (or_ln653_fu_1100_p2 & Range2_all_ones_2_fu_1017_p3);

assign and_ln654_fu_1120_p2 = (carry_1_fu_952_p2 & Range1_all_ones_2_fu_1069_p3);

assign and_ln658_fu_1174_p2 = (xor_ln658_fu_1168_p2 & icmp_ln621_fu_971_p2);

assign and_ln659_fu_1197_p2 = (p_Result_20_fu_963_p3 & deleted_ones_1_fu_1138_p2);

assign and_ln946_fu_290_p2 = (icmp_ln947_fu_270_p2 & icmp_ln946_fu_239_p2);

assign ap_block_pp0_stage0 = ~(1'b1 == 1'b1);

assign ap_block_pp0_stage0_11001 = ~(1'b1 == 1'b1);

assign ap_block_state10_pp0_stage0_iter9 = ~(1'b1 == 1'b1);

assign ap_block_state11_pp0_stage0_iter10 = ~(1'b1 == 1'b1);

assign ap_block_state12_pp0_stage0_iter11 = ~(1'b1 == 1'b1);

assign ap_block_state13_pp0_stage0_iter12 = ~(1'b1 == 1'b1);

assign ap_block_state14_pp0_stage0_iter13 = ~(1'b1 == 1'b1);

assign ap_block_state15_pp0_stage0_iter14 = ~(1'b1 == 1'b1);

assign ap_block_state16_pp0_stage0_iter15 = ~(1'b1 == 1'b1);

assign ap_block_state17_pp0_stage0_iter16 = ~(1'b1 == 1'b1);

assign ap_block_state18_pp0_stage0_iter17 = ~(1'b1 == 1'b1);

assign ap_block_state1_pp0_stage0_iter0 = ~(1'b1 == 1'b1);

assign ap_block_state2_pp0_stage0_iter1 = ~(1'b1 == 1'b1);

assign ap_block_state3_pp0_stage0_iter2 = ~(1'b1 == 1'b1);

assign ap_block_state4_pp0_stage0_iter3 = ~(1'b1 == 1'b1);

assign ap_block_state5_pp0_stage0_iter4 = ~(1'b1 == 1'b1);

assign ap_block_state6_pp0_stage0_iter5 = ~(1'b1 == 1'b1);

assign ap_block_state7_pp0_stage0_iter6 = ~(1'b1 == 1'b1);

assign ap_block_state8_pp0_stage0_iter7 = ~(1'b1 == 1'b1);

assign ap_block_state9_pp0_stage0_iter8 = ~(1'b1 == 1'b1);

assign ashr_ln586_fu_603_p2 = $signed(man_V_fu_547_p3) >>> zext_ln586_fu_599_p1;

assign bitcast_ln702_fu_613_p1 = v_assign_reg_1341_pp0_iter14_reg;

assign bitcast_ln744_fu_444_p1 = LD_fu_440_p1;

assign carry_1_fu_952_p2 = (xor_ln603_fu_946_p2 & and_ln403_fu_885_p2);

assign deleted_ones_1_fu_1138_p2 = (xor_ln621_fu_1132_p2 | deleted_ones_fu_1112_p3);

assign deleted_ones_fu_1112_p3 = ((carry_1_fu_952_p2[0:0] == 1'b1) ? and_ln653_fu_1106_p2 : Range1_all_ones_2_fu_1069_p3);

assign deleted_zeros_fu_1085_p3 = ((carry_1_fu_952_p2[0:0] == 1'b1) ? Range1_all_ones_2_fu_1069_p3 : Range1_all_zeros_1_fu_1077_p3);

assign exp_tmp_fu_471_p4 = {{ireg_fu_455_p1[62:52]}};

assign icmp_ln571_fu_507_p2 = ((trunc_ln555_fu_459_p1 == 63'd0) ? 1'b1 : 1'b0);

assign icmp_ln577_fu_917_p2 = (($signed(F2_reg_1379_pp0_iter15_reg) < $signed(12'd7)) ? 1'b1 : 1'b0);

assign icmp_ln582_fu_826_p2 = ((F2_reg_1379_pp0_iter15_reg == 12'd7) ? 1'b1 : 1'b0);

assign icmp_ln585_fu_573_p2 = ((sh_amt_fu_562_p3 < 12'd54) ? 1'b1 : 1'b0);

assign icmp_ln591_fu_640_p2 = (($signed(add_ln581_fu_552_p2) > $signed(12'd54)) ? 1'b1 : 1'b0);

assign icmp_ln594_fu_663_p2 = (($signed(F2_reg_1379) > $signed(12'd8)) ? 1'b1 : 1'b0);

assign icmp_ln595_1_fu_715_p2 = ((p_Result_10_fu_709_p2 != 54'd0) ? 1'b1 : 1'b0);

assign icmp_ln595_fu_680_p2 = (($signed(add_ln595_fu_675_p2) > $signed(12'd53)) ? 1'b1 : 1'b0);

assign icmp_ln603_fu_589_p2 = ((tmp_7_fu_579_p4 == 7'd0) ? 1'b1 : 1'b0);

assign icmp_ln611_fu_759_p2 = (($signed(add_ln612_fu_754_p2) > $signed(12'd24)) ? 1'b1 : 1'b0);

assign icmp_ln621_1_fu_981_p2 = ((pos1_reg_1462 < 12'd54) ? 1'b1 : 1'b0);

assign icmp_ln621_fu_971_p2 = (($signed(pos1_reg_1462) < $signed(12'd54)) ? 1'b1 : 1'b0);

assign icmp_ln631_1_fu_997_p2 = ((pos2_fu_958_p2 < 12'd54) ? 1'b1 : 1'b0);

assign icmp_ln631_fu_991_p2 = (($signed(pos2_fu_958_p2) < $signed(12'd54)) ? 1'b1 : 1'b0);

assign icmp_ln641_fu_817_p2 = ((Range2_V_1_fu_799_p2 == 54'd0) ? 1'b1 : 1'b0);

assign icmp_ln642_fu_1047_p2 = ((pos2_fu_958_p2 == 12'd54) ? 1'b1 : 1'b0);

assign icmp_ln935_fu_160_p2 = ((input_r_int_reg == 16'd0) ? 1'b1 : 1'b0);

assign icmp_ln946_fu_239_p2 = (($signed(tmp_2_fu_229_p4) > $signed(31'd0)) ? 1'b1 : 1'b0);

assign icmp_ln947_fu_270_p2 = ((p_Result_4_fu_265_p2 != 16'd0) ? 1'b1 : 1'b0);

assign icmp_ln958_fu_315_p2 = (($signed(lsb_index_fu_223_p2) > $signed(32'd0)) ? 1'b1 : 1'b0);

assign ireg_fu_455_p1 = grp_fu_152_p1;

assign lD_fu_782_p3 = man_V_fu_547_p3[sext_ln618_fu_770_p1];


always @ (p_Result_14_fu_198_p3) begin
    if (p_Result_14_fu_198_p3[0] == 1'b1) begin
        l_fu_205_p3 = 32'd0;
    end else if (p_Result_14_fu_198_p3[1] == 1'b1) begin
        l_fu_205_p3 = 32'd1;
    end else if (p_Result_14_fu_198_p3[2] == 1'b1) begin
        l_fu_205_p3 = 32'd2;
    end else if (p_Result_14_fu_198_p3[3] == 1'b1) begin
        l_fu_205_p3 = 32'd3;
    end else if (p_Result_14_fu_198_p3[4] == 1'b1) begin
        l_fu_205_p3 = 32'd4;
    end else if (p_Result_14_fu_198_p3[5] == 1'b1) begin
        l_fu_205_p3 = 32'd5;
    end else if (p_Result_14_fu_198_p3[6] == 1'b1) begin
        l_fu_205_p3 = 32'd6;
    end else if (p_Result_14_fu_198_p3[7] == 1'b1) begin
        l_fu_205_p3 = 32'd7;
    end else if (p_Result_14_fu_198_p3[8] == 1'b1) begin
        l_fu_205_p3 = 32'd8;
    end else if (p_Result_14_fu_198_p3[9] == 1'b1) begin
        l_fu_205_p3 = 32'd9;
    end else if (p_Result_14_fu_198_p3[10] == 1'b1) begin
        l_fu_205_p3 = 32'd10;
    end else if (p_Result_14_fu_198_p3[11] == 1'b1) begin
        l_fu_205_p3 = 32'd11;
    end else if (p_Result_14_fu_198_p3[12] == 1'b1) begin
        l_fu_205_p3 = 32'd12;
    end else if (p_Result_14_fu_198_p3[13] == 1'b1) begin
        l_fu_205_p3 = 32'd13;
    end else if (p_Result_14_fu_198_p3[14] == 1'b1) begin
        l_fu_205_p3 = 32'd14;
    end else if (p_Result_14_fu_198_p3[15] == 1'b1) begin
        l_fu_205_p3 = 32'd15;
    end else if (p_Result_14_fu_198_p3[16] == 1'b1) begin
        l_fu_205_p3 = 32'd16;
    end else if (p_Result_14_fu_198_p3[17] == 1'b1) begin
        l_fu_205_p3 = 32'd17;
    end else if (p_Result_14_fu_198_p3[18] == 1'b1) begin
        l_fu_205_p3 = 32'd18;
    end else if (p_Result_14_fu_198_p3[19] == 1'b1) begin
        l_fu_205_p3 = 32'd19;
    end else if (p_Result_14_fu_198_p3[20] == 1'b1) begin
        l_fu_205_p3 = 32'd20;
    end else if (p_Result_14_fu_198_p3[21] == 1'b1) begin
        l_fu_205_p3 = 32'd21;
    end else if (p_Result_14_fu_198_p3[22] == 1'b1) begin
        l_fu_205_p3 = 32'd22;
    end else if (p_Result_14_fu_198_p3[23] == 1'b1) begin
        l_fu_205_p3 = 32'd23;
    end else if (p_Result_14_fu_198_p3[24] == 1'b1) begin
        l_fu_205_p3 = 32'd24;
    end else if (p_Result_14_fu_198_p3[25] == 1'b1) begin
        l_fu_205_p3 = 32'd25;
    end else if (p_Result_14_fu_198_p3[26] == 1'b1) begin
        l_fu_205_p3 = 32'd26;
    end else if (p_Result_14_fu_198_p3[27] == 1'b1) begin
        l_fu_205_p3 = 32'd27;
    end else if (p_Result_14_fu_198_p3[28] == 1'b1) begin
        l_fu_205_p3 = 32'd28;
    end else if (p_Result_14_fu_198_p3[29] == 1'b1) begin
        l_fu_205_p3 = 32'd29;
    end else if (p_Result_14_fu_198_p3[30] == 1'b1) begin
        l_fu_205_p3 = 32'd30;
    end else if (p_Result_14_fu_198_p3[31] == 1'b1) begin
        l_fu_205_p3 = 32'd31;
    end else begin
        l_fu_205_p3 = 32'd32;
    end
end

assign lsb_index_fu_223_p2 = ($signed(sub_ln944_fu_213_p2) + $signed(32'd4294967272));

assign lshr_ln595_fu_703_p2 = 54'd18014398509481983 >> zext_ln595_fu_699_p1;

assign lshr_ln947_fu_259_p2 = 16'd65535 >> zext_ln947_fu_255_p1;

assign lshr_ln958_fu_358_p2 = zext_ln957_fu_343_p1 >> zext_ln958_fu_355_p1;

assign m_2_fu_374_p2 = (m_fu_364_p3 + zext_ln961_fu_371_p1);

assign m_5_fu_180_p3 = ((p_Result_13_fu_166_p3[0:0] == 1'b1) ? tmp_V_fu_174_p2 : input_r_int_reg);

assign m_6_fu_380_p4 = {{m_2_fu_374_p2[63:1]}};

assign m_fu_364_p3 = ((icmp_ln958_reg_1311[0:0] == 1'b1) ? lshr_ln958_fu_358_p2 : shl_ln959_fu_349_p2);

assign man_V_2_fu_501_p2 = (54'd0 - zext_ln569_fu_497_p1);

assign man_V_fu_547_p3 = ((p_Result_16_reg_1347[0:0] == 1'b1) ? man_V_2_reg_1367 : zext_ln569_reg_1362);

assign neg_src_1_fu_1160_p3 = ((and_ln557_fu_1155_p2[0:0] == 1'b1) ? xor_ln654_fu_1126_p2 : and_ln621_1_fu_1150_p2);

assign or_ln340_1_fu_1228_p2 = (or_ln340_2_fu_1223_p2 | and_ln659_reg_1508);

assign or_ln340_2_fu_1223_p2 = (xor_ln340_fu_1218_p2 | overflow_reg_1502);

assign or_ln340_fu_1213_p2 = (underflow_fu_1208_p2 | overflow_reg_1502);

assign or_ln414_fu_840_p2 = (select_ln594_reg_1445 | r_1_fu_836_p2);

assign or_ln594_fu_721_p2 = (icmp_ln594_fu_663_p2 | icmp_ln591_fu_640_p2);

assign or_ln603_fu_940_p2 = (tmp_10_fu_859_p3 | and_ln603_1_fu_935_p2);

assign or_ln611_fu_1271_p2 = (icmp_ln611_reg_1456_pp0_iter16_reg | icmp_ln571_reg_1372_pp0_iter16_reg);

assign or_ln653_fu_1100_p2 = (tmp_14_fu_1093_p3 | Range1_all_zeros_fu_1036_p2);

assign or_ln658_fu_1180_p2 = (p_Result_20_fu_963_p3 | and_ln658_fu_1174_p2);

assign or_ln_fu_743_p3 = {{10'd513}, {QUAN_INC_reg_1396}};

assign output_V_fu_1282_p3 = ((icmp_ln571_reg_1372_pp0_iter16_reg[0:0] == 1'b1) ? 32'd0 : select_ln611_fu_1275_p3);

assign overflow_fu_1191_p2 = (xor_ln658_1_fu_1186_p2 & or_ln658_fu_1180_p2);

assign p_Result_10_fu_709_p2 = (man_V_fu_547_p3 & lshr_ln595_fu_703_p2);

assign p_Result_13_fu_166_p3 = input_r_int_reg[32'd15];

assign p_Result_14_fu_198_p3 = {{16'd65535}, {p_Result_s_reg_1306}};

assign p_Result_15_fu_428_p5 = {{zext_ln962_fu_390_p1[63:32]}, {tmp_fu_421_p3}, {zext_ln962_fu_390_p1[22:0]}};

assign p_Result_17_fu_489_p3 = {{1'd1}, {trunc_ln565_fu_485_p1}};

assign p_Result_18_fu_655_p3 = man_V_fu_547_p3[zext_ln591_fu_651_p1];

assign p_Result_20_fu_963_p3 = p_Val2_6_fu_927_p3[32'd31];

assign p_Result_3_fu_302_p3 = m_5_reg_1299[add_ln949_fu_296_p2];

assign p_Result_4_fu_265_p2 = (m_5_reg_1299 & lshr_ln947_fu_259_p2);

assign p_Result_5_fu_394_p3 = m_2_fu_374_p2[32'd25];

integer ap_tvar_int_0;

always @ (m_5_fu_180_p3) begin
    for (ap_tvar_int_0 = 16 - 1; ap_tvar_int_0 >= 0; ap_tvar_int_0 = ap_tvar_int_0 - 1) begin
        if (ap_tvar_int_0 > 15 - 0) begin
            p_Result_s_fu_188_p4[ap_tvar_int_0] = 1'b0;
        end else begin
            p_Result_s_fu_188_p4[ap_tvar_int_0] = m_5_fu_180_p3[15 - ap_tvar_int_0];
        end
    end
end

assign p_Val2_4_fu_632_p3 = ((icmp_ln585_fu_573_p2[0:0] == 1'b1) ? trunc_ln586_1_fu_609_p1 : select_ln588_fu_624_p3);

assign p_Val2_5_fu_854_p2 = (p_Val2_4_reg_1430 + zext_ln415_fu_850_p1);

assign p_Val2_6_fu_927_p3 = ((and_ln603_fu_922_p2[0:0] == 1'b1) ? shl_ln604_fu_831_p2 : select_ln403_1_fu_909_p3);

assign pos1_fu_765_p2 = (F2_reg_1379 + 12'd25);

assign pos2_fu_958_p2 = (F2_reg_1379_pp0_iter15_reg + 12'd26);

assign r_1_fu_836_p2 = (or_ln594_reg_1440 & icmp_ln595_1_reg_1435);

assign r_fu_805_p2 = 54'd18014398509481983 >> zext_ln635_fu_795_p1;

assign select_ln340_1_fu_1263_p3 = ((and_ln340_1_fu_1258_p2[0:0] == 1'b1) ? select_ln340_fu_1233_p3 : select_ln388_fu_1240_p3);

assign select_ln340_fu_1233_p3 = ((or_ln340_fu_1213_p2[0:0] == 1'b1) ? 32'd2147483647 : p_Val2_6_reg_1489);

assign select_ln388_fu_1240_p3 = ((underflow_fu_1208_p2[0:0] == 1'b1) ? 32'd2147483648 : p_Val2_6_reg_1489);

assign select_ln403_1_fu_909_p3 = ((and_ln403_1_fu_903_p2[0:0] == 1'b1) ? p_Val2_5_fu_854_p2 : select_ln403_fu_890_p3);

assign select_ln403_fu_890_p3 = ((and_ln403_fu_885_p2[0:0] == 1'b1) ? p_Val2_5_fu_854_p2 : select_ln582_fu_867_p3);

assign select_ln582_fu_867_p3 = ((icmp_ln582_fu_826_p2[0:0] == 1'b1) ? trunc_ln583_reg_1418 : 32'd0);

assign select_ln588_fu_624_p3 = ((tmp_8_fu_616_p3[0:0] == 1'b1) ? 32'd4294967295 : 32'd0);

assign select_ln591_fu_668_p3 = ((icmp_ln591_fu_640_p2[0:0] == 1'b1) ? p_Result_16_reg_1347 : p_Result_18_fu_655_p3);

assign select_ln594_fu_727_p3 = ((or_ln594_fu_721_p2[0:0] == 1'b1) ? select_ln591_fu_668_p3 : p_Result_18_fu_655_p3);

assign select_ln595_fu_691_p3 = ((icmp_ln595_fu_680_p2[0:0] == 1'b1) ? 6'd0 : sub_ln595_fu_686_p2);

assign select_ln611_fu_1275_p3 = ((or_ln611_fu_1271_p2[0:0] == 1'b1) ? select_ln340_1_fu_1263_p3 : p_Val2_6_reg_1489);

assign select_ln642_1_fu_1061_p3 = ((icmp_ln642_fu_1047_p2[0:0] == 1'b1) ? Range1_all_zeros_fu_1036_p2 : xor_ln621_1_fu_976_p2);

assign select_ln642_fu_1053_p3 = ((icmp_ln642_fu_1047_p2[0:0] == 1'b1) ? Range1_all_ones_3_fu_986_p2 : xor_ln621_1_fu_976_p2);

assign select_ln935_fu_448_p3 = ((icmp_ln935_reg_1289_pp0_iter1_reg[0:0] == 1'b1) ? 32'd0 : bitcast_ln744_fu_444_p1);

assign select_ln943_fu_402_p3 = ((p_Result_5_fu_394_p3[0:0] == 1'b1) ? 8'd127 : 8'd126);

assign sext_ln581_fu_823_p1 = sh_amt_reg_1413;

assign sext_ln612_fu_750_p1 = $signed(or_ln_fu_743_p3);

assign sext_ln618_fu_770_p1 = pos1_fu_765_p2;

assign sh_amt_fu_562_p3 = ((QUAN_INC_reg_1396[0:0] == 1'b1) ? add_ln581_fu_552_p2 : sub_ln581_fu_557_p2);

assign shl_ln604_fu_831_p2 = trunc_ln583_reg_1418 << sext_ln581_fu_823_p1;

assign shl_ln959_fu_349_p2 = zext_ln957_fu_343_p1 << zext_ln959_fu_346_p1;

assign sub_ln581_fu_557_p2 = (12'd7 - F2_reg_1379);

assign sub_ln595_fu_686_p2 = ($signed(6'd62) - $signed(trunc_ln595_reg_1403));

assign sub_ln944_fu_213_p2 = (32'd16 - l_fu_205_p3);

assign sub_ln947_fu_249_p2 = (5'd9 - trunc_ln947_fu_245_p1);

assign sub_ln959_fu_321_p2 = (32'd25 - sub_ln944_fu_213_p2);

assign sub_ln964_fu_410_p2 = (8'd6 - trunc_ln943_reg_1331);

assign tmp_10_fu_859_p3 = p_Val2_5_fu_854_p2[32'd31];

assign tmp_13_fu_1003_p3 = pos2_fu_958_p2[32'd11];

assign tmp_14_fu_1093_p3 = pos1_reg_1462[32'd11];

assign tmp_2_fu_229_p4 = {{lsb_index_fu_223_p2[31:1]}};

assign tmp_3_fu_276_p3 = lsb_index_fu_223_p2[32'd31];

assign tmp_6_fu_523_p4 = {{F2_fu_513_p2[11:3]}};

assign tmp_7_fu_579_p4 = {{sh_amt_fu_562_p3[11:5]}};

assign tmp_8_fu_616_p3 = bitcast_ln702_fu_613_p1[32'd31];

assign tmp_V_fu_174_p2 = (16'd0 - input_r_int_reg);

assign tmp_fu_421_p3 = {{p_Result_13_reg_1294_pp0_iter1_reg}, {add_ln964_fu_415_p2}};

assign tobool34_i_i11_fu_333_p2 = (xor_ln949_fu_284_p2 & a_fu_309_p2);

assign trunc_ln555_fu_459_p1 = ireg_fu_455_p1[62:0];

assign trunc_ln565_fu_485_p1 = ireg_fu_455_p1[51:0];

assign trunc_ln575_fu_519_p1 = F2_fu_513_p2[10:0];

assign trunc_ln583_fu_569_p1 = man_V_fu_547_p3[31:0];

assign trunc_ln586_1_fu_609_p1 = ashr_ln586_fu_603_p2[31:0];

assign trunc_ln586_fu_595_p1 = sh_amt_fu_562_p3[5:0];

assign trunc_ln595_fu_539_p1 = F2_fu_513_p2[5:0];

assign trunc_ln619_fu_543_p1 = F2_fu_513_p2[5:0];

assign trunc_ln943_fu_339_p1 = l_fu_205_p3[7:0];

assign trunc_ln944_fu_219_p1 = sub_ln944_fu_213_p2[15:0];

assign trunc_ln947_fu_245_p1 = sub_ln944_fu_213_p2[4:0];

assign underflow_fu_1208_p2 = (xor_ln659_fu_1203_p2 & neg_src_1_reg_1496);

assign xor_ln340_fu_1218_p2 = (neg_src_1_reg_1496 ^ 1'd1);

assign xor_ln403_fu_898_p2 = (p_Result_19_reg_1450 ^ 1'd1);

assign xor_ln571_fu_1247_p2 = (icmp_ln571_reg_1372_pp0_iter16_reg ^ 1'd1);

assign xor_ln582_fu_874_p2 = (icmp_ln582_fu_826_p2 ^ 1'd1);

assign xor_ln603_fu_946_p2 = (or_ln603_fu_940_p2 ^ 1'd1);

assign xor_ln621_1_fu_976_p2 = (tmp_12_reg_1469 ^ 1'd1);

assign xor_ln621_fu_1132_p2 = (icmp_ln621_fu_971_p2 ^ 1'd1);

assign xor_ln654_fu_1126_p2 = (1'd1 ^ and_ln654_fu_1120_p2);

assign xor_ln658_1_fu_1186_p2 = (p_Result_16_reg_1347_pp0_iter15_reg ^ 1'd1);

assign xor_ln658_fu_1168_p2 = (deleted_zeros_fu_1085_p3 ^ 1'd1);

assign xor_ln659_fu_1203_p2 = (1'd1 ^ and_ln659_reg_1508);

assign xor_ln949_fu_284_p2 = (tmp_3_fu_276_p3 ^ 1'd1);

assign zext_ln415_fu_850_p1 = and_ln414_fu_845_p2;

assign zext_ln455_fu_481_p1 = exp_tmp_fu_471_p4;

assign zext_ln569_fu_497_p1 = p_Result_17_fu_489_p3;

assign zext_ln586_fu_599_p1 = trunc_ln586_fu_595_p1;

assign zext_ln591_fu_651_p1 = add_ln591_fu_646_p2;

assign zext_ln595_fu_699_p1 = select_ln595_fu_691_p3;

assign zext_ln635_fu_795_p1 = add_ln635_fu_790_p2;

assign zext_ln947_fu_255_p1 = sub_ln947_fu_249_p2;

assign zext_ln957_fu_343_p1 = m_5_reg_1299_pp0_iter1_reg;

assign zext_ln958_fu_355_p1 = add_ln958_reg_1321;

assign zext_ln959_fu_346_p1 = sub_ln959_reg_1316;

assign zext_ln961_fu_371_p1 = tobool34_i_i11_reg_1326;

assign zext_ln962_fu_390_p1 = m_6_fu_380_p4;

always @ (posedge ap_clk) begin
    zext_ln455_reg_1357[11] <= 1'b0;
    zext_ln569_reg_1362[53:52] <= 2'b01;
end

endmodule //mobilenet_my_exp_fix
