-- Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
-- --------------------------------------------------------------------------------
-- Tool Version: Vivado v.2020.2 (lin64) Build 3064766 Wed Nov 18 09:12:47 MST 2020
-- Date        : Mon Apr 25 03:02:20 2022
-- Host        : cilantro running 64-bit Ubuntu 20.04.4 LTS
-- Command     : write_vhdl -force -mode synth_stub
--               /mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/ip/dbg_fpgarr_pcim_interconnect_ila/dbg_fpgarr_pcim_interconnect_ila_stub.vhdl
-- Design      : dbg_fpgarr_pcim_interconnect_ila
-- Purpose     : Stub declaration of top-level module interface
-- Device      : xcvu9p-flgb2104-2-i
-- --------------------------------------------------------------------------------
library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity dbg_fpgarr_pcim_interconnect_ila is
  Port ( 
    clk : in STD_LOGIC;
    probe0 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe1 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe2 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe3 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe4 : in STD_LOGIC_VECTOR ( 0 to 0 );
    probe5 : in STD_LOGIC_VECTOR ( 159 downto 0 );
    probe6 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe7 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe8 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe9 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe10 : in STD_LOGIC_VECTOR ( 0 to 0 );
    probe11 : in STD_LOGIC_VECTOR ( 159 downto 0 );
    probe12 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe13 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe14 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe15 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe16 : in STD_LOGIC_VECTOR ( 0 to 0 );
    probe17 : in STD_LOGIC_VECTOR ( 159 downto 0 );
    probe18 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe19 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe20 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe21 : in STD_LOGIC_VECTOR ( 31 downto 0 );
    probe22 : in STD_LOGIC_VECTOR ( 0 to 0 );
    probe23 : in STD_LOGIC_VECTOR ( 159 downto 0 )
  );

end dbg_fpgarr_pcim_interconnect_ila;

architecture stub of dbg_fpgarr_pcim_interconnect_ila is
attribute syn_black_box : boolean;
attribute black_box_pad_pin : string;
attribute syn_black_box of stub : architecture is true;
attribute black_box_pad_pin of stub : architecture is "clk,probe0[31:0],probe1[31:0],probe2[31:0],probe3[31:0],probe4[0:0],probe5[159:0],probe6[31:0],probe7[31:0],probe8[31:0],probe9[31:0],probe10[0:0],probe11[159:0],probe12[31:0],probe13[31:0],probe14[31:0],probe15[31:0],probe16[0:0],probe17[159:0],probe18[31:0],probe19[31:0],probe20[31:0],probe21[31:0],probe22[0:0],probe23[159:0]";
attribute X_CORE_INFO : string;
attribute X_CORE_INFO of stub : architecture is "ila,Vivado 2020.2";
begin
end;
