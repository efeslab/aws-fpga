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

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <malloc.h>
#include <poll.h>

#include <utils/sh_dpi_tasks.h>

#ifdef SV_TEST
# include <fpga_pci_sv.h>
#else
# include <fpga_pci.h>
# include <fpga_mgmt.h>
# include "fpga_dma.h"
# include <utils/lcd.h>
#endif

#include "test_dram_dma_common.h"
#include "cl_fpgarr.h"

#define MEM_16G              (1ULL << 34)

void usage(const char* program_name);
int dma_example_hwsw_cosim(int slot_id, size_t buffer_size);

static inline int do_dma_read(int fd, uint8_t *buffer, size_t size,
    uint64_t address, int channel, int slot_id);
static inline int do_dma_write(int fd, uint8_t *buffer, size_t size,
    uint64_t address, int channel, int slot_id);

#if !defined(SV_TEST)
/* use the stdout logger */
const struct logger *logger = &logger_stdout;
#else
# define log_error(...) printf(__VA_ARGS__); printf("\n")
# define log_info(...) printf(__VA_ARGS__); printf("\n")
#endif

/* Main will be different for different simulators and also for C. The
 * definition is in sdk/userspace/utils/include/sh_dpi_tasks.h file */
#if defined(SV_TEST) && defined(INT_MAIN)
/* For cadence and questa simulators main has to return some value */
int test_main(uint32_t *exit_code)

#elif defined(SV_TEST)
void test_main(uint32_t *exit_code)

#else 
int main(int argc, char **argv)

#endif
{
    size_t buffer_size;
#if defined(SV_TEST)
    buffer_size = 2048;
#else
    buffer_size = 1ULL << 24;
#endif

    /* The statements within SCOPE ifdef below are needed for HW/SW
     * co-simulation with VCS */
#if defined(SCOPE)
    svScope scope;
    scope = svGetScopeFromName("tb");
    svSetScope(scope);
#endif

    int rc;
    int slot_id = 0;

#if !defined(SV_TEST)
    switch (argc) {
    case 1:
        break;
    case 3:
        sscanf(argv[2], "%x", &slot_id);
        break;
    default:
        usage(argv[0]);
        return 1;
    }

    /* setup logging to print to stdout */
    rc = log_init("test_dram_dma_hwsw_cosim");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    /* initialize the fpga_plat library */
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");

#endif

    rc = dma_example_hwsw_cosim(slot_id, buffer_size);
    fail_on(rc, out, "DMA example failed");

out:

#if !defined(SV_TEST)
    return rc;
#else
    if (rc != 0) {
        printf("TEST FAILED \n");
    }
    else {
        printf("TEST PASSED \n");
    }
    /* For cadence and questa simulators main has to return some value */
    #ifdef INT_MAIN
    *exit_code = 0;
    return 0;
    #else
    *exit_code = 0;
    #endif
#endif
}

void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}

/**
 * Write 4 identical buffers to the 4 different DRAM channels of the AFI
 */
int dma_example_hwsw_cosim(int slot_id, size_t buffer_size)
{
    uint8_t *host_mem;
    posix_memalign(&host_mem, 64, buffer_size);
    memset(host_mem, 0, buffer_size);
    int rc;

    if (host_mem == NULL) {
        rc = -ENOMEM;
        goto out;
    }

    printf("Memory has been allocated, initializing host_memory...\n");
#if !defined(SV_TEST)
    abort();
    read_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ true);
    fail_on((rc = (read_fd < 0) ? -1 : 0), out, "unable to open read dma queue");

    write_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ false);
    fail_on((rc = (write_fd < 0) ? -1 : 0), out, "unable to open write dma queue");
#else
    uint8_t *trace_buffer = malloc(0x1000000);
    uint64_t trace_buffer_hi = ((uint64_t) trace_buffer >> 32) & 0xffffffff;
    uint64_t trace_buffer_lo = ((uint64_t) trace_buffer) & 0xffffffff;
    uint64_t trace_buffer_size_hi = 0;
    uint64_t trace_buffer_size_lo = 0x1000000;

    // configure csrs via rr_cfg_bus
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_HI), trace_buffer_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_ADDR_LO), trace_buffer_lo);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_HI), trace_buffer_size_hi);
    cl_poke_bar1(RR_CSR_ADDR(BUF_SIZE_LO), trace_buffer_size_lo);
    cl_poke_bar1(RR_CSR_ADDR(BUF_UPDATE), 1);
    cl_poke_bar1(RR_CSR_ADDR(RR_MODE), 0x1); // 0b001

    //init_ddr();
    deselect_atg_hw();

    sv_map_host_memory(host_mem);
    printf("host_mem: %p\n", host_mem);
    cl_poke_ocl(0x001, 0xffffffff);
    cl_poke_ocl(0x030, 0);
    cl_poke_ocl(0x010, 1);
    cl_poke_ocl(0x020, (uint64_t)(host_mem) & 0xffffffff);
    cl_poke_ocl(0x024, ((uint64_t)host_mem >> 32) & 0xffffffff);
    cl_poke_ocl(0x028,0x1234);
    cl_poke_ocl(0x02c,0x5);
    //cl_poke_ocl(0x008,0x1);
    //sv_pause(500);
    //for (uint8_t i = 0; i < 100; ++i) {
    //    printf("[%p]=%#x\n", host_mem+i, host_memory_getc(host_mem+i));
    //}
    rc = 0;
#endif

    cl_poke_bar1(0x100014, 1);

out:
    //if (host_mem != NULL) {
    //    free(host_mem);
    //}
#if !defined(SV_TEST)
    abort();
    if (write_fd >= 0) {
        close(write_fd);
    }
    if (read_fd >= 0) {
        close(read_fd);
    }
#endif
    /* if there is an error code, exit with status 1 */
    return (rc != 0 ? 1 : 0);
}

static inline int do_dma_read(int fd, uint8_t *buffer, size_t size,
    uint64_t address, int channel, int slot_id)
{
#if defined(SV_TEST)
    sv_fpga_start_cl_to_buffer(slot_id, channel, size, (uint64_t) buffer, address);
    return 0;
#else
    return fpga_dma_burst_read(fd, buffer, size, address);
#endif
}

static inline int do_dma_write(int fd, uint8_t *buffer, size_t size,
    uint64_t address, int channel, int slot_id)
{
#if defined(SV_TEST)
    sv_fpga_start_buffer_to_cl(slot_id, channel, size, (uint64_t) buffer, address);
    return 0;
#else
    return fpga_dma_burst_write(fd, buffer, size, address);
#endif
}
