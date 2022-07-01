parallel ../rr_tool.opt.elf -r --phyts-sim {1} :::: <(find ../20220327.output/ -regex .*[^e]_record.dump) | tee record.sim
parallel ../rr_tool.opt.elf -v --phyts-sim {1} :::: <(find ../20220327.output/ -regex .*validate_record.dump) | tee validate.sim
