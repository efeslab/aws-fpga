# This file contains the default configuration for the Nallatech 520N board
# for the use with single precision floating point values.
# To use this configuration file, call cmake with the parameter
#
#     cmake [...] -DHPCC_FPGA_CONFIG="path to this file"
#

set(USE_FPGARR Yes CACHE BOOL "Enable FPGA_RR related target generation" FORCE)
set(USE_MPI No CACHE BOOL "" FORCE)
set(USE_SVM No CACHE BOOL "" FORCE)
set(USE_HBM No CACHE BOOL "" FORCE)
set(FPGA_BOARD_NAME "/mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/Vitis/aws_platform/xilinx_aws-vu9p-f1_shell-v04261818_201920_2/xilinx_aws-vu9p-f1_shell-v04261818_201920_2.xpfm" CACHE STRING "" FORCE)
set(XILINX_LINK_SETTINGS_FILE ${CMAKE_SOURCE_DIR}/settings/notused.ini CACHE
    STRING "" FORCE)
set(XILINX_COMPILE_SETTINGS_FILE ${CMAKE_SOURCE_DIR}/settings/notused.ini CACHE
    STRING "" FORCE)

# FFT specific options
set(LOG_FFT_SIZE 19 CACHE STRING "Log2 of the used FFT size" FORCE)
set(NUM_REPLICATIONS 1 CACHE STRING "Number of kernel replications" FORCE)
#set(INTEL_CODE_GENERATION_SETTINGS ${CMAKE_SOURCE_DIR}/settings/settings.gen.intel.fft1d_float_8.svm.py CACHE FILEPATH "" FORCE)
