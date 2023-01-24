start_gui
open_hw_manager
connect_hw_server -url efesfpga.ddns.net:3121
open_hw_target -xvc_url 127.0.0.1:10201
set BUILDDIR $::env(HDK_DIR)/cl/examples/cl_axis_fifo_buggy/build/checkpoints
set BUILDID "22_03_26-015201"
set debugbridgeID "debug_bridge_0"
set_property PROBES.FILE ${BUILDDIR}/${BUILDID}.debug_probes.ltx [get_hw_devices ${debugbridgeID}]
set_property FULL_PROBES.FILE ${BUILDDIR}/${BUILDID}.debug_probes.ltx [get_hw_devices ${debugbridgeID}]
refresh_hw_device [lindex [get_hw_devices $debugbridgeID] 0]
display_hw_ila_data [ get_hw_ila_data hw_ila_data_1 -of_objects [get_hw_ilas -of_objects [get_hw_devices ${debugbridgeID}] -filter {CELL_NAME=~"WRAPPER_INST/SH/SH/MGT_TOP/SH_ILA_0"}]]
