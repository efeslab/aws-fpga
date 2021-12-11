open_project proj -reset

add_files hls/face_detect.cpp
add_files hls/haar_dataEWC_with_partitioning.h
add_files hls/haar_dataRcc_with_partitioning.h
add_files hls/haar_mapping.h

add_files -tb hls/face_detect.h
add_files -tb hls/check_result.cpp
add_files -tb hls/check_result.h
add_files -tb hls/face_detect_host.cpp
add_files -tb hls/image0_320_240.h
add_files -tb hls/image.cpp
add_files -tb hls/image.h
add_files -tb hls/typedefs.h
add_files -tb hls/utils.cpp
add_files -tb hls/utils.h

set_top face_detect

open_solution -flow_target vitis solution -reset

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

csynth_design
cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all -compiled_library_dir "/home/jcma/aws-fpga/hdk/cl/examples/cl_hls/verif/sim/vcs/vcs_complib"
