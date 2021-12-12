open_project -reset proj

add_files hls/conv_1x1_fl.cc
add_files hls/conv_3x3_group_fl.cc
add_files hls/net_hls.cc
add_files hls/net_hls.h
add_files -tb hls/output_verify.cc
add_files -tb hls/reorder_weight.cc
add_files -tb hls/tb.cc -cflags "-g"


set_top mobilenet

open_solution -reset -flow_target vitis solution

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

#csim_design -O
csynth_design
cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all -compiled_library_dir "/tmp/vcs_complib"
