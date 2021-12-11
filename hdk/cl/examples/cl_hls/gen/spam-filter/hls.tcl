open_project -reset proj

add_files hls/lut.h
add_files hls/sgd.cpp
add_files hls/sgd.h

add_files -tb hls/check_result.cpp
add_files -tb hls/check_result.h
add_files -tb hls/spam_filter.cpp
add_files -tb hls/typedefs.h
add_files -tb hls/utils.cpp
add_files -tb hls/utils.h

set_top SgdLR

open_solution -reset -flow_target vitis solution

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

#csim_design -argv "-p /home/jcma/rosetta/spam-filter/data"
csynth_design
cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all -argv "-p /home/jcma/rosetta/spam-filter/data"
