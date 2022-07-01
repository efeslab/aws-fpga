import sys
import re
from statistics import mean, geometric_mean

lines = sys.stdin.read()
# line is
# Simulating 64b counters, Baseline(bits) 5396574384, additional_cost(bits) 1081376512, 20.038203%
baseline = []
additional_cost = []
cost_ratio = []
for line in lines.splitlines():
    fields = re.split(r'[^0-9.]+', line)
    b = int(fields[2])
    a = int(fields[3])
    baseline.append(b)
    additional_cost.append(a)
    cost_ratio.append(a/b)
sum_baseline = sum(baseline)
sum_additional_cost = sum(additional_cost)
print(f"avg: {sum_additional_cost/sum_baseline * 100}%, max: {max(cost_ratio)}, geomean {geometric_mean(cost_ratio)}, mean {mean(cost_ratio)}")
