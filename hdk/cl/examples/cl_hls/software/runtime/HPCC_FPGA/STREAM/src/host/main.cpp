//
// Created by Marius Meyer on 04.12.19.
//

#include "stream_benchmark.hpp"
#include "fpgarropencl.h"

using namespace stream;

static const char *test_argv_array[] = {
    "arg0",
    "-s",
    "128"
};
REG_STATIC_ARGV(test_argv_array);
/**
The program entry point
*/
int
fpgarropencl_main(int argc, char *argv[]) {
    // Setup benchmark
    StreamBenchmark bm(argc, argv);
    bool success = bm.executeBenchmark();
    if (success) {
        return 0;
    }
    else {
        return 1;
    }
}

