include_directories(${gtest_SOURCE_DIR}/include ${gtest_SOURCE_DIR})
include_directories(${CMAKE_BINARY_DIR}/src/common)

if (INTELFPGAOPENCL_FOUND)
    include_directories(SYSTEM ${IntelFPGAOpenCL_INCLUDE_DIRS})
    add_executable(${HOST_EXE_NAME}_test_intel ${TEST_SOURCES} ${PROJECT_SOURCES})
    target_link_libraries(${HOST_EXE_NAME}_test_intel gtest gmock ${LIB_NAME}_intel ${IntelFPGAOpenCL_LIBRARIES} "${OpenMP_CXX_FLAGS}")
    target_link_libraries(${HOST_EXE_NAME}_test_intel hpcc_fpga_base_test)
    add_dependencies(${HOST_EXE_NAME}_test_intel ${kernel_emulation_targets_intel})
    target_compile_definitions(${HOST_EXE_NAME}_test_intel PRIVATE -DINTEL_FPGA)
    if (USE_SVM)
        target_compile_definitions(${HOST_EXE_NAME}_test_intel PRIVATE -DCL_VERSION_2_0)
    endif()
    target_compile_options(${HOST_EXE_NAME}_test_intel PRIVATE "${OpenMP_CXX_FLAGS}")
    foreach (kernel_target ${kernel_emulation_targets_intel})
        set(additional_commands "")
        string(REPLACE "_intel" ".aocx" kernel_name ${kernel_target})
        add_test(NAME test_unit_${kernel_target} COMMAND $<TARGET_FILE:${HOST_EXE_NAME}_test_intel> ${additional_commands} -f ${kernel_name} ${TEST_HOST_FLAGS} WORKING_DIRECTORY ${EXECUTABLE_OUTPUT_PATH})
    endforeach(kernel_target)
endif()

if (Vitis_FOUND)
    include_directories(SYSTEM ${Vitis_INCLUDE_DIRS})
    add_executable(${HOST_EXE_NAME}_test_xilinx ${TEST_SOURCES} ${PROJECT_SOURCES})
    target_link_libraries(${HOST_EXE_NAME}_test_xilinx gtest gmock ${LIB_NAME}_xilinx ${Vitis_LIBRARIES} "${OpenMP_CXX_FLAGS}")
    target_link_libraries(${HOST_EXE_NAME}_test_xilinx hpcc_fpga_base_test)
    add_dependencies(${HOST_EXE_NAME}_test_xilinx ${kernel_emulation_targets_xilinx})
    target_compile_definitions(${HOST_EXE_NAME}_test_xilinx PRIVATE -DXILINX_FPGA)
    target_compile_options(${HOST_EXE_NAME}_test_xilinx PRIVATE "${OpenMP_CXX_FLAGS}")
    foreach (kernel_target ${kernel_emulation_targets_xilinx})
        string(REPLACE "_xilinx" ".xclbin" kernel_name ${kernel_target})
        add_test(NAME test_unit_${kernel_target} COMMAND $<TARGET_FILE:${HOST_EXE_NAME}_test_xilinx> -f ${kernel_name} ${TEST_HOST_FLAGS} WORKING_DIRECTORY ${EXECUTABLE_OUTPUT_PATH})
    endforeach(kernel_target)
endif()