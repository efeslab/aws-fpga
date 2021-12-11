open_project -reset proj

add_files hls/digitrec.cpp
add_files hls/digitrec.h
add_files hls/typedefs.h
add_files -tb hls/check_result.cpp
add_files -tb hls/check_result.h
add_files -tb hls/digit_recognition.cpp
add_files -tb hls/testing_data.h
add_files -tb hls/training_data.h
add_files -tb hls/typedefs.h
add_files -tb hls/utils.cpp
add_files -tb hls/utils.h

set_top DigitRec

open_solution -reset -flow_target vitis solution

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

csynth_design
#cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all
