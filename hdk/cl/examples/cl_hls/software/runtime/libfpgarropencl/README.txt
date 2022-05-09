Why did I decide to write an OpenCL wrapper?
In general OpenCL follows the way of compiling program from binary then
programing the device. The Xilinx XRT framework is the only OpenCL lib provided
by Xilinx as far as I know. The given AWS F1 OpenCL example relies on the
interaction between the XRT framework and some FPGA platform image provided by
Amazon without source code (so I could not change it).
Since I could not integrate FPGARR with the FPGA-side AWS paltform wrapper, I
could not deal with applications workflows like the OpenCL programming binary to
devices.
The XRT simulation example also uses the OpenCL `build->program binary`
workflow.

I decided to write an OpenCL wrapper that can work with the `Vitis_HLS` generated verilog in both VCS simulation and on real hardware.
I think that approach is better than hack more into the XRT framework.


#Usage
1. Use the Makefile to generate .a library at current directory
2. Use the Makefile.inc to config other applications to link with the .a library
