// cwd: /mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/hdk/cl/examples/cl_fpgarr/design
// automatically generated by scripts/cl_fpgarr_autogrouping.py


`UNPACKED_LOGGING_BUS_GROUP2(merge_0, rr_sda_SH2CL_logging_bus, rr_ocl_SH2CL_logging_bus);

`UNPACKED_LOGGING_BUS_GROUP2(merge_1, merge_0, rr_bar1_SH2CL_logging_bus);

`UNPACKED_LOGGING_BUS_GROUP2(merge_2, merge_1, rr_pcim_SH2CL_logging_bus);

`UNPACKED_LOGGING_BUS_GROUP2(merged_SH2CL_logging_bus, merge_2, rr_dma_pcis_SH2CL_logging_bus);
