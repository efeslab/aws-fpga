# Add fpgarr source code to the target directory.
# fpgarr project
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_defs.svh                 $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_dbg.svh                  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_types.svh                $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_pkg.sv                   $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_utils.sv                 $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_axi_rr.sv                $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_axil_rr.sv               $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/twowayhandshake_logger.sv          $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/twowayhandshake_replayer.sv        $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/transkidbuf.sv                     $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/transkidbuf_pipeline.sv            $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/axichannel_logger.sv               $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/axichannel_replayer.sv             $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_packing.sv               $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_packing_cfg.svh          $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_happenbefore_encoder.sv  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_csrs.sv                  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_tracedecoder.sv          $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_chgrouping.sv            $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_rr_sel.sv                $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_rt_loge_crossbar.sv      $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_int_to_pcim.sv           $TARGET_DIR
## fpgarr tracestorage files
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_tracestorage_axi.sv      $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_tracestorage_wrapper.sv  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_tracestorage_wrapper_writeonly.sv  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_tracestorage_encoder.sv  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_tracestorage_decoder.sv  $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_pcim_interconnect.sv     $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_irq_pcim_interconnect.sv $TARGET_DIR
file copy -force $CL_FPGARR_ROOT/design/merged_fifo.sv                     $TARGET_DIR
### parameterized fifo
file copy -force $CL_FPGARR_ROOT/design/lib/xpm_fifo_sync_wrapper.sv       $TARGET_DIR

# fpgarr top module
file copy -force $CL_FPGARR_ROOT/design/cl_fpgarr_wrapper.sv               $TARGET_DIR

set CL_MODULE cl_fpgarr_wrapper
