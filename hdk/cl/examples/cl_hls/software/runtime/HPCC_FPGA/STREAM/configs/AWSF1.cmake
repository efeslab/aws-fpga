# This file contains the default configuration for the Xilinx U280 board
# for the use with single precision floating point values.
# To use this configuration file, call cmake with the parameter
#
#     cmake [...] -DHPCC_FPGA_CONFIG="path to this file"
#

set(USE_FPGARR Yes CACHE BOOL "Enable FPGA_RR related target generation" FORCE)
set(USE_SVM No CACHE BOOL "" FORCE)
set(USE_HBM No CACHE BOOL "" FORCE)
set(USE_MPI No CACHE BOOL "" FORCE)
set(FPGA_BOARD_NAME "/mnt/storage/gefeizuo/FPGA/FPGARR/aws-fpga/Vitis/aws_platform/xilinx_aws-vu9p-f1_shell-v04261818_201920_2/xilinx_aws-vu9p-f1_shell-v04261818_201920_2.xpfm" CACHE STRING "" FORCE)
set(XILINX_LINK_SETTINGS_FILE ${CMAKE_SOURCE_DIR}/settings/notused.ini CACHE
    STRING "" FORCE)
set(XILINX_COMPILE_SETTINGS_FILE ${CMAKE_SOURCE_DIR}/settings/notused.ini CACHE
    STRING "" FORCE)

# STREAM specific options
# Defaults to a total of ~12GB data
set(DEFAULT_ARRAY_LENGTH 536870912 CACHE STRING "" FORCE)
set(VECTOR_COUNT 16 CACHE STRING "" FORCE)
set(GLOBAL_MEM_UNROLL 1 CACHE STRING "" FORCE)
set(NUM_REPLICATIONS 1 CACHE STRING "" FORCE)
set(DEVICE_BUFFER_SIZE 2048 CACHE STRING "" FORCE)

# Set the data type since optional vector types are used
set(DATA_TYPE float CACHE STRING "" FORCE)
set(HOST_DATA_TYPE cl_${DATA_TYPE} CACHE STRING "" FORCE)
if (VECTOR_COUNT GREATER 1)
    set(DEVICE_DATA_TYPE ${DATA_TYPE}${VECTOR_COUNT} CACHE STRING "" FORCE)
else()
    set(DEVICE_DATA_TYPE ${DATA_TYPE} CACHE STRING "" FORCE)
endif()
