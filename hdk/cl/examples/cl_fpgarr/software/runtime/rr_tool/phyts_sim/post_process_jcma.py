import sys
import re
from statistics import mean, geometric_mean

record_lines = open("record.sim").readlines()
validate_lines = open("validate.sim").readlines()

assert(len(record_lines) == len(validate_lines))

baseline = []
additional_cost = []
cost_ratio = []
per_tests_stat = {}
test_name = None
rr_type = None

for i in range(0, len(record_lines)):
    rl = record_lines[i]
    vl = validate_lines[i]
    if rl.endswith(".dump\n"):
        assert(vl.endswith(".dump\n"))
        test_name, rr_type = re.findall(r"/([a-zA-Z0-9_.]+)_[0-9]{2}_(.*).dump", rl)[0]
    else:
        rfields = re.split(r'[^0-9.]+', rl)
        rb = int(rfields[2])
        ra = int(rfields[3])

        vfields = re.split(r'[^0-9.]+', vl)
        vb = int(vfields[2])
        va = int(vfields[3])

        baseline.append(rb + vb)
        additional_cost.append(ra + va)
        ratio = (ra + va) / (rb + vb)
        cost_ratio.append(ratio)
        per_tests_stat.setdefault(test_name, {}).setdefault("total", []).append(ratio)
sum_baseline = sum(baseline)
sum_additional_cost = sum(additional_cost)
print(f"avg: {sum_additional_cost/sum_baseline * 100}%, max: {max(cost_ratio)}, geomean {geometric_mean(cost_ratio)}, mean {mean(cost_ratio)}")

print("Name\tgeomean(total_cost_ratio)")
for test_name in sorted(per_tests_stat.keys()):
    total_cost_ratio = per_tests_stat[test_name]["total"]
    print(f"{test_name}\t{geometric_mean(total_cost_ratio)}")



#
## line is
## ../20220327.output/test_dram_dma_01_validate_record.dump
## Simulating 64b counters, Baseline(bits) 5396574384, additional_cost(bits) 1081376512, 20.038203%
#baseline = []
#additional_cost = []
#cost_ratio = []
#per_tests_stat = {}
#test_name = None
#rr_type = None
#for line in lines.splitlines():
#    if line.endswith(".dump"):
#        # rr_type is "record" or "validate_record"
#        test_name, rr_type = re.findall(r"/([a-zA-Z0-9_.]+)_[0-9]{2}_(.*).dump", line)[0]
#    else:
#        fields = re.split(r'[^0-9.]+', line)
#        b = int(fields[2])
#        a = int(fields[3])
#        baseline.append(b)
#        additional_cost.append(a)
#        ratio = a/b
#        cost_ratio.append(ratio)
#        per_tests_stat.setdefault(test_name,{}).setdefault(rr_type,[]).append(ratio)
#sum_baseline = sum(baseline)
#sum_additional_cost = sum(additional_cost)
#print(f"avg: {sum_additional_cost/sum_baseline * 100}%, max: {max(cost_ratio)}, geomean {geometric_mean(cost_ratio)}, mean {mean(cost_ratio)}")
#
#print("Name\tgeomean(record_cost_ratio)\tgeomean(validate_cost_ratio)")
#for test_name in sorted(per_tests_stat.keys()):
#    record_cost_ratio = per_tests_stat[test_name]["record"]
#    validate_cost_ratio = per_tests_stat[test_name]["validate_record"]
#    print(f"{test_name}\t{geometric_mean(record_cost_ratio)}\t{geometric_mean(validate_cost_ratio)}")
