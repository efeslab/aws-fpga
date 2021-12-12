open_project -reset proj

add_files hls/bf_kernel.cl

set_top bellman_ford

open_solution -reset -flow_target vitis solution

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

csynth_design
