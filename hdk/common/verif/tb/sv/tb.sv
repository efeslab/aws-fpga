// Amazon FPGA Hardware Development Kit
//
// Copyright 2016 Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Amazon Software License (the "License"). You may not use
// this file except in compliance with the License. A copy of the License is
// located at
//
//    http://aws.amazon.com/asl/
//
// or in the "license" file accompanying this file. This file is distributed on
// an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
// implied. See the License for the specific language governing permissions and
// limitations under the License.

module tb();

   parameter NUM_HMC = 4;
   parameter NUM_PCIE = 1;
   parameter NUM_GTY = 4;
   parameter NUM_I2C = 2;
   parameter NUM_POWER = 4;


   
   // This is poortly documented in AWS docs
   // My take-away:
   // Common things: you can either use c_host_memory (need to comply with
   // the virtual memory abstraction) or sv_host_memory (embedded in the sv
   // world and handled by the simulator, starting from addr 0x0)
   // For c_host_memory, all access should use virtual memory addresses and the
   // sv_map_host_meory does nothing besides remembering "yeah, we are using
   // c_host_memory so do not use sv_host_memory from now on".
   // For sv_map_host_memory, all access should be managed just like you need to
   // allocate the physical DDR address (start from 0) on a real FPGA.
   //
   // However, without my patch: PCIS and PCIM cannot be simulated correctly at
   // the same time, since once c_host_memory is used (i.e. called
   // sv_map_host_memory), all memory access including pcis will use the
   // c_host_memory, thus blow-up the memory address management.
   //
   // With my patch: PCIS related operations will be forced to use
   // sv_host_memory and the rest is untouched (i.e. use sv_host_memory if no
   // c_host_memory is available)
   logic [31:0]         sv_host_memory[*];
   logic                use_c_host_memory = 1'b0;
   
`ifdef VCS
initial begin
   if (!$test$plusargs("NO_WAVES")) begin
      $vcdpluson;
      $vcdplusmemon;
   end
end
`endif

`include "sh_dpi_tasks.svh"
   
   card card();
   
endmodule // tb

`ifdef XILINX_SIMULATOR
  module short(in1, in1);
    inout in1;
  endmodule
`endif

