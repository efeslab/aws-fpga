
set(COMPILER_INCLUDES "-I${CMAKE_BINARY_DIR}/src/common/" "-I${CMAKE_CURRENT_SOURCE_DIR}")

set(Vitis_EMULATION_CONFIG_UTIL $ENV{XILINX_VITIS}/bin/emconfigutil)

if (CMAKE_BUILD_TYPE EQUAL "Debug")
        set(VPP_FLAGS "-O0 -g")
else()
        set(VPP_FLAGS "-O3")
endif()

##
# This function will create build targets for the kernels for emulationand synthesis for xilinx.
##
function(generate_kernel_targets_xilinx)
    foreach (kernel_file_name ${ARGN})
        string(REGEX MATCH "^custom_.*" is_custom_kernel ${kernel_file_name})
        if (is_custom_kernel) 
                string(REPLACE "custom_" "" base_file_name ${kernel_file_name})
                set(base_file_part "src/device/custom/${base_file_name}")
        else()
                set(base_file_part "src/device/${kernel_file_name}")
        endif()
        set(base_file "${CMAKE_SOURCE_DIR}/${base_file_part}.cl")
        if (KERNEL_REPLICATION_ENABLED)
            set(source_f "${CMAKE_BINARY_DIR}/${base_file_part}_replicated_xilinx.cl")
        else()
            set(source_f "${CMAKE_BINARY_DIR}/${base_file_part}_copied_xilinx.cl")
        endif()
        set(bitstream_compile xilinx_tmp_compile/${kernel_file_name}.xo)
        set(bitstream_compile_emulate xilinx_tmp_compile/${kernel_file_name}_emulate.xo)
        set(bitstream_emulate_f
            ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_emulate.xclbin)
        set(bitstream_f ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}.xclbin)
        file(MAKE_DIRECTORY ${CMAKE_BINARY_DIR}/settings)
        if (XILINX_GENERATE_LINK_SETTINGS)
	    set(gen_xilinx_link_settings ${XILINX_LINK_SETTINGS_FILE})
            set(xilinx_link_settings ${CMAKE_BINARY_DIR}/settings/settings.link.xilinx.${kernel_file_name}.ini)
        else()
            set(gen_xilinx_link_settings ${XILINX_LINK_SETTINGS_FILE})
            set(xilinx_link_settings ${CMAKE_BINARY_DIR}/settings/settings.link.xilinx.${kernel_file_name}.ini)
        endif()
        set(xilinx_report_folder "${EXECUTABLE_OUTPUT_PATH}/xilinx_reports")
        set(local_CLFLAGS ${CLFLAGS} -DXILINX_FPGA)
        list(APPEND local_CLFLAGS --report_dir=${xilinx_report_folder} --log_dir=${xilinx_report_folder}/logs)

        string(REGEX MATCH "^.+\.tcl" is_tcl_script ${XILINX_COMPILE_SETTINGS_FILE})
        if (is_tcl_script)
                set(CLFLAGS --hls.pre_tcl ${XILINX_COMPILE_SETTINGS_FILE})
        else()
                set(CLFLAGS --config ${XILINX_COMPILE_SETTINGS_FILE})
        endif()

        # build emulation config for device
        add_custom_command(OUTPUT ${EXECUTABLE_OUTPUT_PATH}/emconfig.json
        COMMAND ${Vitis_EMULATION_CONFIG_UTIL} -f ${FPGA_BOARD_NAME} --od ${EXECUTABLE_OUTPUT_PATH}
        )
        if (XILINX_GENERATE_LINK_SETTINGS)
            add_custom_command(OUTPUT ${xilinx_link_settings}
                    COMMAND ${Python3_EXECUTABLE} ${CODE_GENERATOR} -o ${xilinx_link_settings} -p num_replications=${NUM_REPLICATIONS} --comment "\"#\"" --comment-ml-start "\"$$\"" --comment-ml-end "\"$$\"" ${gen_xilinx_link_settings}
                    MAIN_DEPENDENCY ${gen_xilinx_link_settings}
                    )
        else()
                add_custom_command(OUTPUT ${xilinx_link_settings}
                        COMMAND cp ${gen_xilinx_link_settings} ${xilinx_link_settings}
                        MAIN_DEPENDENCY ${gen_xilinx_link_settings}
                        )
        endif()

        if (KERNEL_REPLICATION_ENABLED)
                add_custom_command(OUTPUT ${source_f}
                        COMMAND ${Python3_EXECUTABLE} ${CODE_GENERATOR} -o ${source_f} -p num_replications=1 -p num_total_replications=${NUM_REPLICATIONS} ${base_file}
                        MAIN_DEPENDENCY ${base_file}
                )
        else()
                add_custom_command(OUTPUT ${source_f}
                        COMMAND cp ${base_file} ${source_f}
                        MAIN_DEPENDENCY ${base_file}
                )
        endif()

        add_custom_command(OUTPUT ${bitstream_compile_emulate}
                COMMAND ${Vitis_COMPILER} ${local_CLFLAGS} ${VPP_FLAGS} -DEMULATE -t sw_emu ${COMPILER_INCLUDES} ${XILINX_ADDITIONAL_COMPILE_FLAGS} -f ${FPGA_BOARD_NAME} -g -c ${XILINX_COMPILE_FLAGS} -o ${bitstream_compile_emulate} ${source_f}
                MAIN_DEPENDENCY ${source_f}
                DEPENDS ${XILINX_COMPILE_SETTINGS_FILE}
                )
        add_custom_command(OUTPUT ${bitstream_emulate_f}
            COMMAND ${Vitis_COMPILER} ${local_CL_FLAGS} ${VPP_FLAGS} -DEMULATE -t sw_emu ${COMPILER_INCLUDES} ${XILINX_ADDITIONAL_LINK_FLAGS} -f ${FPGA_BOARD_NAME} -g -l --config ${xilinx_link_settings} ${XILINX_COMPILE_FLAGS} -o ${bitstream_emulate_f} ${bitstream_compile_emulate}
                MAIN_DEPENDENCY ${bitstream_compile_emulate}
                DEPENDS ${xilinx_link_settings}
                )
        add_custom_command(OUTPUT ${bitstream_compile}
                COMMAND ${Vitis_COMPILER} ${local_CLFLAGS} ${VPP_FLAGS} -t hw ${COMPILER_INCLUDES} ${XILINX_ADDITIONAL_COMPILE_FLAGS}  --platform ${FPGA_BOARD_NAME} -R2 -c ${XILINX_COMPILE_FLAGS} -o ${bitstream_compile} ${source_f}
                MAIN_DEPENDENCY ${source_f}
                DEPENDS ${XILINX_COMPILE_SETTINGS_FILE}
                )
        add_custom_command(OUTPUT ${bitstream_f}
                COMMAND ${Vitis_COMPILER} ${local_CLFLAGS} ${VPP_FLAGS} -t hw ${COMPILER_INCLUDES} ${XILINX_ADDITIONAL_LINK_FLAGS} --platform ${FPGA_BOARD_NAME} -R2 -l --config ${xilinx_link_settings} ${XILINX_COMPILE_FLAGS} -o ${bitstream_f} ${bitstream_compile}
                MAIN_DEPENDENCY ${bitstream_compile}
                DEPENDS ${xilinx_link_settings}
                )
        add_custom_target(${kernel_file_name}_emulate_xilinx 
		DEPENDS ${bitstream_emulate_f} 
                DEPENDS ${source_f} ${CMAKE_BINARY_DIR}/src/common/parameters.h ${EXECUTABLE_OUTPUT_PATH}/emconfig.json)
        add_custom_target(${kernel_file_name}_xilinx
		DEPENDS ${bitstream_f} 
                DEPENDS ${CMAKE_BINARY_DIR}/src/common/parameters.h
                )
        add_custom_target(${kernel_file_name}_report_xilinx
		DEPENDS ${bitstream_compile} 
                DEPENDS ${CMAKE_BINARY_DIR}/src/common/parameters.h
                )
        list(APPEND kernel_emulation_targets_xilinx ${kernel_file_name}_emulate_xilinx)
        set(kernel_emulation_targets_xilinx ${kernel_emulation_targets_xilinx} CACHE INTERNAL "Kernel emulation targets used to define dependencies for the tests for Xilinx devices")
    endforeach ()
endfunction()


##
# This function will create build targets for the kernels for emulation, reports and synthesis.
# It will use the generate_kernel_replication function to generate a new code file containing the code for all kernels
##
function(generate_kernel_targets_intel)
    foreach (kernel_file_name ${ARGN})
        string(REGEX MATCH "^custom_.*" is_custom_kernel ${kernel_file_name})
        if (is_custom_kernel) 
                string(REPLACE "custom_" "" base_file_name ${kernel_file_name})
                set(base_file_part "src/device/custom/${base_file_name}")
        else()
                set(base_file_part "src/device/${kernel_file_name}")
        endif()
        set(base_file "${CMAKE_SOURCE_DIR}/${base_file_part}.cl")
        if (KERNEL_REPLICATION_ENABLED)
            set(source_f "${CMAKE_BINARY_DIR}/${base_file_part}_replicated_intel.cl")
        else()
            set(source_f "${CMAKE_BINARY_DIR}/${base_file_part}_copied_intel.cl")
        endif()
        set(report_f ${kernel_file_name}_report_intel/reports/report.html)
        set(bitstream_emulate_f ${kernel_file_name}_emulate.aocx)
        set(bitstream_f ${kernel_file_name}.aocx)
        if (KERNEL_REPLICATION_ENABLED)
                set(codegen_parameters -p num_replications=${NUM_REPLICATIONS} -p num_total_replications=${NUM_REPLICATIONS})
                if (INTEL_CODE_GENERATION_SETTINGS)
                        list(APPEND codegen_parameters -p "\"use_file('${INTEL_CODE_GENERATION_SETTINGS}')\"")
                endif()
                add_custom_command(OUTPUT ${source_f}
                        COMMAND ${Python3_EXECUTABLE} ${CODE_GENERATOR} -o ${source_f} ${codegen_parameters} ${base_file}
                        MAIN_DEPENDENCY ${base_file}
                        )
        else()
                add_custom_command(OUTPUT ${source_f}
                        COMMAND cp ${base_file} ${source_f}
                        MAIN_DEPENDENCY ${base_file}
                )
        endif()
        add_custom_command(OUTPUT ${EXECUTABLE_OUTPUT_PATH}/${bitstream_emulate_f}
                COMMAND ${CMAKE_COMMAND} -E copy  ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_emulate_f} ${EXECUTABLE_OUTPUT_PATH}/${bitstream_emulate_f}
                DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_emulate_f}
        )
        add_custom_command(OUTPUT ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_reports/report.html
                COMMAND ${CMAKE_COMMAND} -E copy_directory  ${CMAKE_CURRENT_BINARY_DIR}/${kernel_file_name}_report_intel/reports/ ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_reports/
                DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${report_f}
        )
        add_custom_command(OUTPUT ${EXECUTABLE_OUTPUT_PATH}/${bitstream_f}
                COMMAND ${CMAKE_COMMAND} -E copy  ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_f} ${EXECUTABLE_OUTPUT_PATH}/${bitstream_f} 
                COMMAND ${CMAKE_COMMAND} -E copy_directory ${CMAKE_CURRENT_BINARY_DIR}/${kernel_file_name}/reports ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_synth_reports
                COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/${kernel_file_name}/acl_quartus_report.txt ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_synth_reports/acl_quartus_report.txt
                COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/${kernel_file_name}/quartus_sh_compile.log ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_synth_reports/quartus_sh_compile.log
                COMMAND ${CMAKE_COMMAND} -E copy ${CMAKE_CURRENT_BINARY_DIR}/${kernel_file_name}/${kernel_file_name}.log ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_synth_reports/${kernel_file_name}.log
                DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_f}
        )
        add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_emulate_f}
                COMMAND ${IntelFPGAOpenCL_AOC} ${source_f} -DEMULATE -DINTEL_FPGA ${COMPILER_INCLUDES} ${AOC_FLAGS} -march=emulator
                -o ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_emulate_f}
                MAIN_DEPENDENCY ${source_f}
                DEPENDS ${CMAKE_BINARY_DIR}/src/common/parameters.h
                )
        add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_f}
                COMMAND ${IntelFPGAOpenCL_AOC} ${source_f} -DINTEL_FPGA ${COMPILER_INCLUDES} ${AOC_FLAGS} -board=${FPGA_BOARD_NAME}
                -o ${CMAKE_CURRENT_BINARY_DIR}/${bitstream_f}
                MAIN_DEPENDENCY ${source_f}
                DEPENDS ${CMAKE_BINARY_DIR}/src/common/parameters.h
                )
        add_custom_command(OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/${report_f}
                COMMAND ${IntelFPGAOpenCL_AOC} ${source_f} -DINTEL_FPGA ${COMPILER_INCLUDES} ${AOC_FLAGS} -rtl -report -board=${FPGA_BOARD_NAME}
                -o ${kernel_file_name}_report_intel
                MAIN_DEPENDENCY ${source_f}
                DEPENDS ${CMAKE_BINARY_DIR}/src/common/parameters.h
                )
        add_custom_target(${kernel_file_name}_report_intel 
                DEPENDS ${EXECUTABLE_OUTPUT_PATH}/${kernel_file_name}_reports/report.html)
        add_custom_target(${kernel_file_name}_intel 
                DEPENDS ${EXECUTABLE_OUTPUT_PATH}/${bitstream_f})
        add_custom_target(${kernel_file_name}_emulate_intel 
                DEPENDS ${EXECUTABLE_OUTPUT_PATH}/${bitstream_emulate_f})
        list(APPEND kernel_emulation_targets_intel ${kernel_file_name}_emulate_intel)
        set(kernel_emulation_targets_intel ${kernel_emulation_targets_intel} CACHE INTERNAL "Kernel emulation targets used to define dependencies for the tests for intel devices")
    endforeach ()
endfunction()
