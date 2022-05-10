open_project -reset proj.vitis_hls

add_files hls/nbody.cpp
add_files hls/utils.hpp
add_files hls/nbody.hpp
#add_files -tb $SRC_DIR/main-cl.cpp
#add_files -tb $SRC_DIR/parser.cpp
#add_files -tb $SRC_DIR/parser.hpp
#add_files -tb $SRC_DIR/support.hpp

set_top nbody

open_solution -reset -flow_target vitis solution

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 32 -m_axi_max_write_burst_length 32

csynth_design
#cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all
