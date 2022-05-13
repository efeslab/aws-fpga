# CL_HLS FPGARR benchmark
Remember to patch `Vitis_HLS_2020.2_include.patch` before generating RTL from
the HLS.

# About HLS Generation
For simulation, use the `export_design` to export a zip then extract.
For synthesis, pay attention to .tcl files related to ip that locate inside
the `$project/solution/syn/verilog` directory. source those tcl in the synthesis
scripts.
