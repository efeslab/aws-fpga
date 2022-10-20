parallel -k "echo {1} && ../rr_tool.opt.elf -r --phyts-sim {1}" :::: <(find ../20220327.output/ -regex .*[^e]_record.dump | sort) | tee record.sim
parallel -k "echo {1} && ../rr_tool.opt.elf -v --phyts-sim {1}" :::: <(find ../20220327.output/ -regex .*validate_record.dump | sort) | tee validate.sim
