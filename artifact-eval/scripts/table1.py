#/usr/bin/python3

import os
import glob
from sh import grep, tail
import argparse
import statistics as stat
from typing import List
from utils import geomean_of_percent
from config import benchmarks

HOME = os.getenv("HOME")
parser = argparse.ArgumentParser(description="Reproduce the Table.1 in the paper")
parser.add_argument('--expr-output', type=str, required=True, help="The output directory of experiments on the actual FPGA hardware")
parser.add_argument('--record-width', type=int, default=1694, help="The width (in bits) of the interfaces being recorded (default: %(default)s)")

args = parser.parse_args()
DRAM_OUTPUT_DIR = args.expr_output
HLS_OUTPUT_DIR  = args.expr_output

# sanity check
assert(os.path.exists(DRAM_OUTPUT_DIR))
assert(os.path.exists(HLS_OUTPUT_DIR))

def check_file_existance(f):
    if not os.path.exists(f):
        raise RuntimeError(f"Does {f} exist?")

def get_elaspsed_ns(f):
    check_file_existance(f)
    elapsed_time = grep("RR pre_rr->post_rr, elapsed ns:", f).split()[-1]
    user_elapsed_time = grep("RR user timer, elapsed ns:", f).split()[-1]
    if int(user_elapsed_time) == 0:
        return int(elapsed_time)
    else:
        return int(user_elapsed_time)

def get_hb_violation(f):
    check_file_existance(f)
    res = tail("-n1", f).replace(":", " ").replace(","," ").split()
    hb_mismatches = float(res[6].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    total_violations = float(res[9].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    content_mismatches = float(res[-1].replace("%", "").replace("(", " ").replace(")", " ").split()[1])
    return hb_mismatches, total_violations, content_mismatches

def get_record_size(f):
    check_file_existance(f)
    record_buffer_size = grep("Record Buffer", f).replace("(","").replace(")","").split()[-2]
    validate_buffer_size = grep("Validate Buffer", f).replace("(","").replace(")","").split()[-2]
    return int(record_buffer_size) + int(validate_buffer_size)

print("{},{},{},{},{},{},{},{}".format(
    "benchmark", "avg(runtime)(ms)", "avg(overhead) (%)", "std(overhead) (%)",
    "avg(trace size) (B)", "Trace Reduction",
    "hb violation (%)", "std(hb violation) (%)"
))

for benchName, benchID in benchmarks.items():
    if benchName == "test_dram_dma":
        OUTPUT_DIR = DRAM_OUTPUT_DIR
    else:
        OUTPUT_DIR = HLS_OUTPUT_DIR
    runtime = []
    perf_overhead = []
    hb_violation = []
    trace_sizeB = []
    glob_pattern = f"{OUTPUT_DIR}/{benchName}*_diff.txt"
    matched_prefix = [path[:-len('diff.txt')] for path in glob.glob(glob_pattern)]
    if len(matched_prefix) == 0:
        # skip non-exist benchmark results
        print(f"skip non-exists benchmark: {benchName}")
        continue
    for bench_prefix in matched_prefix:
        none_ns    = get_elaspsed_ns(bench_prefix + "none.log")
        recordv_ns = get_elaspsed_ns(bench_prefix + "recordv.log")
        replayv_ns = get_elaspsed_ns(bench_prefix + "replayv.log")
        record_sizeB = get_record_size(bench_prefix + "recordv.log")
        hbm, totv, contm = get_hb_violation(bench_prefix + "diff.txt")
        runtime.append(float(none_ns)/1000/1000)
        perf_overhead.append((float(recordv_ns) - float(none_ns)) / float(none_ns) * 100.0)
        hb_violation.append(totv)
        trace_sizeB.append(record_sizeB)

    #perf_overhead = np.array(perf_overhead)
    #hb_violation = np.array(hb_violation)

    mean_runtime = stat.mean(runtime)
    mean_trace_sizeB = stat.mean(trace_sizeB)
    cycles = (mean_runtime / 10**3) * 250 * 10**6 # 250MHz
    cycle_accurate_trace_sizeB = cycles * args.record_width // 8
    trace_size_reduction = int(cycle_accurate_trace_sizeB // mean_trace_sizeB)
    print("{},{},{},{},{},{},{},{}".format(
        benchName,
        mean_runtime,
        geomean_of_percent([overhead + 100 for overhead in perf_overhead]) - 100, stat.stdev(perf_overhead),
        mean_trace_sizeB, trace_size_reduction,
        stat.mean(hb_violation), stat.stdev(hb_violation),
    ))
