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
#include <assert.h>

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
    buffer_size = (1ULL << 15);
// should be $clog2(buffer_size)
#define PCIM_BUF_ALIGNMENT (1ULL << 15)
#else
    buffer_size = 1ULL << 24;
#define PCIM_BUF_ALIGNMENT (1ULL << 24)
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
#ifdef SV_TEST
#define TEST_PCIM
#define TEST_PCIS
#endif
int dma_example_hwsw_cosim(int slot_id, size_t buffer_size)
{
    errno = 0;
    int rc;
#ifdef TEST_PCIS
    uint8_t *write_buffer = malloc(buffer_size);
    uint8_t *read_buffer = malloc(buffer_size);
    if (write_buffer == NULL || read_buffer == NULL) {
        rc = -ENOMEM;
        goto out;
    }
    setup_send_rdbuf_to_c(read_buffer, buffer_size);
    int write_fd, read_fd;
    write_fd = -1;
    read_fd = -1;
#endif // TEST_PCIS

    uint8_t *host_mem;
    posix_memalign((void*)(&host_mem), PCIM_BUF_ALIGNMENT, buffer_size);
    memset(host_mem, 0, buffer_size);

    if (host_mem == NULL) {
        rc = -ENOMEM;
        goto out;
    }

    printf("Memory has been allocated, initializing host_memory...\n");
#if !defined(SV_TEST)
    int read_fd, write_fd;
    abort();
    read_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ true);
    fail_on((rc = (read_fd < 0) ? -1 : 0), out, "unable to open read dma queue");

    write_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ false);
    fail_on((rc = (write_fd < 0) ? -1 : 0), out, "unable to open write dma queue");
#else

#if defined(TEST_PCIM) || defined(TEST_PCIS)
    printf("Starting DDR init...\n");
    init_ddr();
    printf("Done DDR init...\n");
#endif
    rc = init_rr(0);
    fail_on(rc, out, "init_rr failed");
    do_pre_rr();

    if (is_record()) {
        deselect_atg_hw();

#ifdef TEST_PCIM
        // {{{ setup test for pcim
        sv_map_host_memory(host_mem);
        printf("host_mem: %p\n", host_mem);
        // 0x30: A value of 0 will drive PCIS/XDMA transactions to DDR.
        cl_poke_ocl(0x030, 0);
        //Offset 0x10:
        //     15:0 - Write Num Inst - Number of write instructions
        //     31:16 - Read Num inst - Number of read instructions
        cl_poke_ocl(0x010, 1);
        // Offset 0x1c: Write Index  - Write instruction Index
        cl_poke_ocl(0x01c, 0);
        // Offset 0x20: Write address low - Write instruction address
        cl_poke_ocl(0x020, (uint64_t)(host_mem) & 0xffffffff);
        // Offset 0x24: Write address high - Write instruction address
        cl_poke_ocl(0x024, ((uint64_t)host_mem >> 32) & 0xffffffff);
        // Offset 0x28: Write data - Write instruction start data.  All other data will be incrementing or PRBS
        cl_poke_ocl(0x028,0x1234);
        // Offset 0x2c: Write length/User - Write instruction length (number of data phases.  note there are no partial data phases)
        //     7:0 - Length -- this is the number of AXI data phases.   Lower address bits define first data offset
        //     15:8 - Last data adj -- Number of DW to adj last data phase (0 means all DW are valid, 1 means all but 1DW valid, etc...)
        //     31:16 - User
        //NOTE: This should not exceed the sh_cl_cfg_max_payload
        uint32_t wr_burst = 2; // max is 8
        uint32_t sizeB_burst = wr_burst*64;
        uint8_t wraddr_inc_shift = 7;
        assert((1 << wraddr_inc_shift) == sizeB_burst);
        uint32_t Nloop = buffer_size / sizeB_burst;
        cl_poke_ocl(0x02c, wr_burst - 1);
        // Offset 0x00, check test_dram_dma_common.h for details
        pcim_tst_cfg_t tstcfg = {
            .continuous = 1,
            .incLoopData = 1,
            .PRBS = 0,
            .readCompEn = 0,
            .syncEn = 0,
            .iterMode = 1,
            .loopHiAddrEn = 1,
            .userIDMode = 0,
            .wrAddrLoopShift = wraddr_inc_shift,
            .rdAddrLoopShift = 0,
            .rsvd = 0,
            .incIDMode = 0,
            .constData = 0,
            .unused = 0
        };
        cl_poke_ocl(0x00, tstcfg.val);
        //Offset 0xc0: Write Loop count low - In loop mode number of times loop
        //Offset 0xc4: Write Loop count high
        cl_poke_ocl(0xc0, Nloop);
        cl_poke_ocl(0xc4, 0x00);
        //Offset 0x08:
        //     0 - Write Go (read back write in progress) - Write this bit to start executing the write instructions.  Reads back '1' while write instructions are in progress.
        //     1 - Read Go (read back write in progress) - Write this bit to start executing the read instructions.  Reads back '1' while read instructions are in progress.
        //     2 - Read response pending (read only).  REad only, reads back '1' while read responses are pending.
        cl_poke_ocl(0x008,0x1);
        // }}} end of set for pcim
#endif
        
#ifdef TEST_PCIS
        // {{{setup test for pcis
        printf("filling buffer with  random data...\n") ;

        rc = fill_buffer_urandom(write_buffer, buffer_size);
        fail_on(rc, out, "unable to initialize buffer");

        printf("Now performing the DMA transactions...\n");
        for (int dimm = 0; dimm < 4; dimm++) {
            rc = do_dma_write(write_fd, write_buffer, buffer_size,
                dimm * MEM_16G, dimm, slot_id);
            fail_on(rc, out, "DMA write failed on DIMM: %d", dimm);
        }

        bool passed = true;
        for (int dimm = 0; dimm < 4; dimm++) {
            rc = do_dma_read(read_fd, read_buffer, buffer_size,
                dimm * MEM_16G, dimm, slot_id);
            fail_on(rc, out, "DMA read failed on DIMM: %d", dimm);
            uint64_t differ = buffer_compare(read_buffer, write_buffer, buffer_size);
            if (differ != 0) {
                log_error("DIMM %d failed with %lu bytes which differ", dimm, differ);
                passed = false;
            } else {
                log_info("DIMM %d passed!", dimm);
            }
        }
        rc = (passed) ? 0 : 1;
#else
        rc = 0;
#endif
        // }}} end of test for pcis

        // wait for pcim test to finish
#ifdef TEST_PCIM
        sv_pause(1);
        for (uint8_t i = 0; i < 100; ++i) {
            printf("[%p]=%#x\n", host_mem+i, host_memory_getc(host_mem+i));
        }
        rc = rc || 0;
#else
        rc = 0;
#endif
    }
#endif // end of SV_TEST

    do_post_rr();

out:
    free(host_mem);
#ifdef TEST_PCIS
    if (write_buffer != NULL) {
        free(write_buffer);
    }
    if (read_buffer != NULL) {
        free(read_buffer);
    }
#endif
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
