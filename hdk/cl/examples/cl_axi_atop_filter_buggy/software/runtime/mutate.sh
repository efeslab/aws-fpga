#!/bin/bash
RR_TOOL=../../../cl_fpgarr/software/runtime/rr_tool/rr_tool.opt.elf
cp record.dump original_record.dump
${RR_TOOL} -r -a original_record.dump -d > original_record.txt
${RR_TOOL} -m original_record.dump -m validate_record.dump -o test.dump
${RR_TOOL} -r -a test.dump -d > test.txt
cp test.dump mutated_record.dump
