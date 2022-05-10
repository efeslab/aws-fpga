-- ==============================================================
-- RTL generated by Vitis HLS - High-Level Synthesis from C, C++ and OpenCL v2020.2 (64-bit)
-- Version: 2020.2
-- Copyright (C) Copyright 1986-2020 Xilinx, Inc. All Rights Reserved.
-- 
-- ===========================================================

library IEEE;
use IEEE.std_logic_1164.all;
use IEEE.numeric_std.all;

entity nbody_core_start_entry38 is
port (
    ap_clk : IN STD_LOGIC;
    ap_rst : IN STD_LOGIC;
    ap_start : IN STD_LOGIC;
    ap_done : OUT STD_LOGIC;
    ap_continue : IN STD_LOGIC;
    ap_idle : OUT STD_LOGIC;
    ap_ready : OUT STD_LOGIC;
    x_val_dout : IN STD_LOGIC_VECTOR (63 downto 0);
    x_val_empty_n : IN STD_LOGIC;
    x_val_read : OUT STD_LOGIC;
    y_val_dout : IN STD_LOGIC_VECTOR (63 downto 0);
    y_val_empty_n : IN STD_LOGIC;
    y_val_read : OUT STD_LOGIC;
    z_val_dout : IN STD_LOGIC_VECTOR (63 downto 0);
    z_val_empty_n : IN STD_LOGIC;
    z_val_read : OUT STD_LOGIC;
    EPS_dout : IN STD_LOGIC_VECTOR (31 downto 0);
    EPS_empty_n : IN STD_LOGIC;
    EPS_read : OUT STD_LOGIC;
    x_val_out_din : OUT STD_LOGIC_VECTOR (31 downto 0);
    x_val_out_full_n : IN STD_LOGIC;
    x_val_out_write : OUT STD_LOGIC;
    x_val_out1_din : OUT STD_LOGIC_VECTOR (63 downto 0);
    x_val_out1_full_n : IN STD_LOGIC;
    x_val_out1_write : OUT STD_LOGIC;
    y_val_out_din : OUT STD_LOGIC_VECTOR (31 downto 0);
    y_val_out_full_n : IN STD_LOGIC;
    y_val_out_write : OUT STD_LOGIC;
    y_val_out2_din : OUT STD_LOGIC_VECTOR (63 downto 0);
    y_val_out2_full_n : IN STD_LOGIC;
    y_val_out2_write : OUT STD_LOGIC;
    z_val_out_din : OUT STD_LOGIC_VECTOR (31 downto 0);
    z_val_out_full_n : IN STD_LOGIC;
    z_val_out_write : OUT STD_LOGIC;
    z_val_out3_din : OUT STD_LOGIC_VECTOR (63 downto 0);
    z_val_out3_full_n : IN STD_LOGIC;
    z_val_out3_write : OUT STD_LOGIC;
    EPS_out_din : OUT STD_LOGIC_VECTOR (31 downto 0);
    EPS_out_full_n : IN STD_LOGIC;
    EPS_out_write : OUT STD_LOGIC;
    EPS_out4_din : OUT STD_LOGIC_VECTOR (31 downto 0);
    EPS_out4_full_n : IN STD_LOGIC;
    EPS_out4_write : OUT STD_LOGIC );
end;


architecture behav of nbody_core_start_entry38 is 
    constant ap_const_logic_1 : STD_LOGIC := '1';
    constant ap_const_logic_0 : STD_LOGIC := '0';
    constant ap_ST_fsm_state1 : STD_LOGIC_VECTOR (0 downto 0) := "1";
    constant ap_const_lv32_0 : STD_LOGIC_VECTOR (31 downto 0) := "00000000000000000000000000000000";
    constant ap_const_boolean_1 : BOOLEAN := true;

attribute shreg_extract : string;
    signal ap_done_reg : STD_LOGIC := '0';
    signal ap_CS_fsm : STD_LOGIC_VECTOR (0 downto 0) := "1";
    attribute fsm_encoding : string;
    attribute fsm_encoding of ap_CS_fsm : signal is "none";
    signal ap_CS_fsm_state1 : STD_LOGIC;
    attribute fsm_encoding of ap_CS_fsm_state1 : signal is "none";
    signal x_val_blk_n : STD_LOGIC;
    signal y_val_blk_n : STD_LOGIC;
    signal z_val_blk_n : STD_LOGIC;
    signal EPS_blk_n : STD_LOGIC;
    signal x_val_out_blk_n : STD_LOGIC;
    signal x_val_out1_blk_n : STD_LOGIC;
    signal y_val_out_blk_n : STD_LOGIC;
    signal y_val_out2_blk_n : STD_LOGIC;
    signal z_val_out_blk_n : STD_LOGIC;
    signal z_val_out3_blk_n : STD_LOGIC;
    signal EPS_out_blk_n : STD_LOGIC;
    signal EPS_out4_blk_n : STD_LOGIC;
    signal ap_block_state1 : BOOLEAN;
    signal ap_NS_fsm : STD_LOGIC_VECTOR (0 downto 0);
    signal ap_ce_reg : STD_LOGIC;


begin




    ap_CS_fsm_assign_proc : process(ap_clk)
    begin
        if (ap_clk'event and ap_clk =  '1') then
            if (ap_rst = '1') then
                ap_CS_fsm <= ap_ST_fsm_state1;
            else
                ap_CS_fsm <= ap_NS_fsm;
            end if;
        end if;
    end process;


    ap_done_reg_assign_proc : process(ap_clk)
    begin
        if (ap_clk'event and ap_clk =  '1') then
            if (ap_rst = '1') then
                ap_done_reg <= ap_const_logic_0;
            else
                if ((ap_continue = ap_const_logic_1)) then 
                    ap_done_reg <= ap_const_logic_0;
                elsif ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
                    ap_done_reg <= ap_const_logic_1;
                end if; 
            end if;
        end if;
    end process;


    ap_NS_fsm_assign_proc : process (ap_start, ap_done_reg, ap_CS_fsm, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        case ap_CS_fsm is
            when ap_ST_fsm_state1 => 
                ap_NS_fsm <= ap_ST_fsm_state1;
            when others =>  
                ap_NS_fsm <= "X";
        end case;
    end process;

    EPS_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, EPS_empty_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            EPS_blk_n <= EPS_empty_n;
        else 
            EPS_blk_n <= ap_const_logic_1;
        end if; 
    end process;


    EPS_out4_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            EPS_out4_blk_n <= EPS_out4_full_n;
        else 
            EPS_out4_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    EPS_out4_din <= EPS_dout;

    EPS_out4_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            EPS_out4_write <= ap_const_logic_1;
        else 
            EPS_out4_write <= ap_const_logic_0;
        end if; 
    end process;


    EPS_out_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, EPS_out_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            EPS_out_blk_n <= EPS_out_full_n;
        else 
            EPS_out_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    EPS_out_din <= EPS_dout;

    EPS_out_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            EPS_out_write <= ap_const_logic_1;
        else 
            EPS_out_write <= ap_const_logic_0;
        end if; 
    end process;


    EPS_read_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            EPS_read <= ap_const_logic_1;
        else 
            EPS_read <= ap_const_logic_0;
        end if; 
    end process;

    ap_CS_fsm_state1 <= ap_CS_fsm(0);

    ap_block_state1_assign_proc : process(ap_start, ap_done_reg, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
                ap_block_state1 <= ((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1));
    end process;


    ap_done_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            ap_done <= ap_const_logic_1;
        else 
            ap_done <= ap_done_reg;
        end if; 
    end process;


    ap_idle_assign_proc : process(ap_start, ap_CS_fsm_state1)
    begin
        if (((ap_start = ap_const_logic_0) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            ap_idle <= ap_const_logic_1;
        else 
            ap_idle <= ap_const_logic_0;
        end if; 
    end process;


    ap_ready_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            ap_ready <= ap_const_logic_1;
        else 
            ap_ready <= ap_const_logic_0;
        end if; 
    end process;


    x_val_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            x_val_blk_n <= x_val_empty_n;
        else 
            x_val_blk_n <= ap_const_logic_1;
        end if; 
    end process;


    x_val_out1_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_out1_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            x_val_out1_blk_n <= x_val_out1_full_n;
        else 
            x_val_out1_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    x_val_out1_din <= x_val_dout;

    x_val_out1_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            x_val_out1_write <= ap_const_logic_1;
        else 
            x_val_out1_write <= ap_const_logic_0;
        end if; 
    end process;


    x_val_out_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_out_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            x_val_out_blk_n <= x_val_out_full_n;
        else 
            x_val_out_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    x_val_out_din <= x_val_dout(32 - 1 downto 0);

    x_val_out_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            x_val_out_write <= ap_const_logic_1;
        else 
            x_val_out_write <= ap_const_logic_0;
        end if; 
    end process;


    x_val_read_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            x_val_read <= ap_const_logic_1;
        else 
            x_val_read <= ap_const_logic_0;
        end if; 
    end process;


    y_val_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, y_val_empty_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            y_val_blk_n <= y_val_empty_n;
        else 
            y_val_blk_n <= ap_const_logic_1;
        end if; 
    end process;


    y_val_out2_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, y_val_out2_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            y_val_out2_blk_n <= y_val_out2_full_n;
        else 
            y_val_out2_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    y_val_out2_din <= y_val_dout;

    y_val_out2_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            y_val_out2_write <= ap_const_logic_1;
        else 
            y_val_out2_write <= ap_const_logic_0;
        end if; 
    end process;


    y_val_out_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, y_val_out_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            y_val_out_blk_n <= y_val_out_full_n;
        else 
            y_val_out_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    y_val_out_din <= y_val_dout(32 - 1 downto 0);

    y_val_out_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            y_val_out_write <= ap_const_logic_1;
        else 
            y_val_out_write <= ap_const_logic_0;
        end if; 
    end process;


    y_val_read_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            y_val_read <= ap_const_logic_1;
        else 
            y_val_read <= ap_const_logic_0;
        end if; 
    end process;


    z_val_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, z_val_empty_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            z_val_blk_n <= z_val_empty_n;
        else 
            z_val_blk_n <= ap_const_logic_1;
        end if; 
    end process;


    z_val_out3_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, z_val_out3_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            z_val_out3_blk_n <= z_val_out3_full_n;
        else 
            z_val_out3_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    z_val_out3_din <= z_val_dout;

    z_val_out3_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            z_val_out3_write <= ap_const_logic_1;
        else 
            z_val_out3_write <= ap_const_logic_0;
        end if; 
    end process;


    z_val_out_blk_n_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, z_val_out_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            z_val_out_blk_n <= z_val_out_full_n;
        else 
            z_val_out_blk_n <= ap_const_logic_1;
        end if; 
    end process;

    z_val_out_din <= z_val_dout(32 - 1 downto 0);

    z_val_out_write_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            z_val_out_write <= ap_const_logic_1;
        else 
            z_val_out_write <= ap_const_logic_0;
        end if; 
    end process;


    z_val_read_assign_proc : process(ap_start, ap_done_reg, ap_CS_fsm_state1, x_val_empty_n, y_val_empty_n, z_val_empty_n, EPS_empty_n, x_val_out_full_n, x_val_out1_full_n, y_val_out_full_n, y_val_out2_full_n, z_val_out_full_n, z_val_out3_full_n, EPS_out_full_n, EPS_out4_full_n)
    begin
        if ((not(((ap_start = ap_const_logic_0) or (z_val_out3_full_n = ap_const_logic_0) or (z_val_out_full_n = ap_const_logic_0) or (y_val_out2_full_n = ap_const_logic_0) or (y_val_out_full_n = ap_const_logic_0) or (x_val_out1_full_n = ap_const_logic_0) or (x_val_out_full_n = ap_const_logic_0) or (z_val_empty_n = ap_const_logic_0) or (ap_const_logic_0 = EPS_out4_full_n) or (ap_const_logic_0 = EPS_out_full_n) or (ap_const_logic_0 = EPS_empty_n) or (y_val_empty_n = ap_const_logic_0) or (x_val_empty_n = ap_const_logic_0) or (ap_done_reg = ap_const_logic_1))) and (ap_const_logic_1 = ap_CS_fsm_state1))) then 
            z_val_read <= ap_const_logic_1;
        else 
            z_val_read <= ap_const_logic_0;
        end if; 
    end process;

end behav;