open_project -reset proj.vitis_hls

add_files stream_kernels_single_replicated_xilinx.cl
add_files parameters.h

set_top calc_0

open_solution -reset -flow_target vitis solution

set_part {xcvu9p-flgb2104-2-i}

create_clock -period "250MHz" -name default

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 32 -m_axi_max_write_burst_length 32

csynth_design
#cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all
export_design -rtl verilog -format sysgen -output .
