1. `DMA_PCIS` interface, the backpressure signals are essential similar to Intel's AlmostFull. The Timeout Detection block (from Shell) can still issue 16 transactions after the backpressure is asserted (e.g. de-asserting AxVALID).
2. `rr_cfg_bus` address mapping allocation. Since AXI interconnect only supports
   the power of 2 size of address range, I can only split OCL (32MB) to two 16MB
   range, which is too much waste. So I decided to split bar1 (2MB) and use the
   higher 1MB as the `rr_cfg_bus`.

3. Setup: Used installer `Xilinx_Unified_2020.2_1118_1232` to install the suite
   of Xilinx tools (vitis + `vitis_HLS` + vivado). Installed XRT 2020.2 (ignore
   the dkms driver error on cilantro during installation, since I will not use
   the actural runtime to communicate with a real FPGA card, I do not care this
   kernel driver (it is most likely due to kernel version issue)). Also symlink
   unwrapped vrs from `Vivado` to `Vitis_HLS`
4. Apply `xpm_fifo` related patch to the 2020.2 Vivado installation. The patch
   is at `cl_fpgarr/design/lib/xpm_fifo_sync_wrapper.sim.patch`
5. When update the userspace tool, remember to execute
   `sdk/userspace/mkall_fpga_mgmt_tools.sh` then
   `sdk/userspace/install_fpga_mgmt_tools.sh`
6. How to syntesize HLS benchmarks:
   `HLS_DESIGN=face_detection ./aws_build_dcp_from_cl.sh`
   remember to `export CL_DIR=xxx/cl_hls`
7. `dram_dma` simulation: `make AXI_MEMORY_MODEL=1 VCS=1 C_TEST=test_dram_dma_hwsw_cosim RR_MODE=none/record(v)/replay(v) /compile/run`
   hls simulation: `make HLS_DESIGN=mobilenet VCS=1 AXI_MEMORY_MODEL=1 RR_MODE=none PARAM_PATH=~/iSmartDNN/params_384_320_160_v2.bin FIG_PATH=~/iSmartDNN/1.bin`
8. on hardware debug. start xilinx HW server on the f1 instance, then in vivado:
   `connect_hw_server -url efesfpga.ddns.net:3121 -allow_non_jtag`
   `open_hw_target -xvc_url 127.0.0.1:10201`
9. Apply xilinx patch `https://support.xilinx.com/s/article/76960?language=en_US`
10. Compile XRT with ubuntu 20.04 g++-7 to get rid of symbol `_ZNSt7__cxx1118basic_stringstreamIcSt11char_traitsIcESaIcEEC1Ev@@GLIBCXX_3.4.26`
11. Autogen py scripts (execute from the `cl_fpgarr/design` dir)
   - `./scripts/cl_fpgarr_autogrouping.py --help` to see docs
   - `./scripts/sweep_mergetree.sh --ddrc --app_axim` to configue which interfaces to include/exclude
