#!/bin/bash

sudo fpga-clear-local-image -S 0
sudo fpga-load-local-image -S 0 -I agfi-0e7b0fe35b155e88c
sudo RR_MODE=recordv ./axis_fifo_hw.elf | tee -a log.txt
sudo fpga-clear-local-image -S 0
sudo fpga-load-local-image -S 0 -I agfi-0e7b0fe35b155e88c
sudo RR_MODE=replayv ./axis_fifo_hw.elf | tee -a log.txt
/home/jcma/aws-fpga/hdk/cl/examples/cl_fpgarr/software/runtime/rr_tool/rr_tool.opt.elf -v -c validate_record.dump -c validate_replay.dump --hbver2 -d | tee -a log.txt
