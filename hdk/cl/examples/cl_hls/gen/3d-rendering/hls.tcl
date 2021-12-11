open_project -reset proj

add_files hls/rendering.cpp
add_files hls/typedefs.h
add_files -tb hls/3d_rendering_host.cpp
add_files -tb hls/check_result.cpp
add_files -tb hls/check_result.h
add_files -tb hls/input_data.h
add_files -tb hls/typedefs.h

set_top rendering

open_solution -reset -flow_target vitis solution

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

csynth_design
#cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all
