#=========================================================================
# hls.tcl
#=========================================================================

set top "top"
set cflags "-DHLS_COMPILE -O3 -std=c++0x -I../utils"
set tbflags "-DHLS_COMPILE -O3 -std=c++0x -I../utils -lminizip -lz"
set utils "../utils/Common.cpp ../utils/DataIO.cpp ../utils/ParamIO.cpp ../utils/ZipIO.cpp ../utils/Timer.cpp"

open_project hls.prj

set_top $top

add_files Accel.cpp -cflags $cflags
add_files -tb accel_test_random.cpp -cflags $tbflags
add_files -tb AccelSchedule.cpp -cflags $cflags
add_files -tb AccelTest.cpp -cflags $cflags
add_files -tb AccelPrint.cpp -cflags $cflags
add_files -tb InputConv.cpp -cflags $tbflags
add_files -tb Dense.cpp -cflags $tbflags
add_files -tb $utils -cflags $tbflags

open_solution "solution1" -reset

set_part "xcvu9p-flgb2104-2-i"
create_clock -period "250MHz"

config_rtl -reset state
config_interface -m_axi_addr64 -m_axi_max_bitwidth 512 -m_axi_min_bitwidth 512 -m_axi_max_read_burst_length 16 -m_axi_max_write_burst_length 16

# Apply optimizations
source opt.tcl

csim_design

csynth_design
cosim_design -rtl verilog -trace_level all -tool vcs -wave_debug

#export_design -evaluate verilog

exit
