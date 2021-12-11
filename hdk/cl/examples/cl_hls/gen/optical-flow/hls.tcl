set cflags "-I$::env(VITIS_LIBRARIES)/vision/L1/include"

open_project proj -reset

add_files hls/optical_flow.cpp -cflags $cflags
add_files hls/optical_flow.h

add_files -tb hls/check_result.cpp
add_files -tb hls/check_result.h
add_files -tb hls/optical_flow_host.cpp
add_files -tb hls/typedefs.h
add_files -tb hls/utils.cpp
add_files -tb hls/utils.h
add_files -tb hls/Convert.cpp
add_files -tb hls/Convert.h
add_files -tb hls/Convolve.cpp
add_files -tb hls/Convolve.h
add_files -tb hls/Copyright.h
add_files -tb hls/Error.h
add_files -tb hls/Image.cpp
add_files -tb hls/Image.h
add_files -tb hls/ImageIO.cpp
add_files -tb hls/ImageIO.h
add_files -tb hls/imageLib.h
add_files -tb hls/README.txt
add_files -tb hls/RefCntMem.cpp
add_files -tb hls/RefCntMem.h
add_files -tb hls/flowIO.h
add_files -tb hls/flowIO.cpp


set_top optical_flow

open_solution solution -reset

set_part "xcvu9p-flgb2104-2-i"

create_clock -period "250MHz"

config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16 

#csim_design -argv "-p /home/jcma/rosetta/optical-flow/datasets/current -o /home/jcma/rosetta/optical-flow/out.flo"
csynth_design
cosim_design -tool vcs -wave_debug -rtl verilog -trace_level all -compiled_library_dir "/home/jcma/aws-fpga/hdk/cl/examples/cl_hls/verif/sim/vcs/vcs_complib" -argv "-p /home/jcma/rosetta/optical-flow/datasets/current -o /home/jcma/rosetta/optical-flow/out.flo"

