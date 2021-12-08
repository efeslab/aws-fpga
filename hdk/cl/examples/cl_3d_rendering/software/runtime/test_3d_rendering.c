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

#include "test_common.h"
#include "typedefs.h"
#include "input_data.h"
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
    buffer_size = 128;
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

int interrupt_polling(int interrupt_number) {
    struct pollfd fds[1];
    uint32_t fd;
    char event_file_name[256];
    int device_num = 0;
    int rc = 0, rd = 0;

    rc = sprintf(event_file_name, "/dev/xdma%i_events_%i", device_num, interrupt_number);
    fail_on((rc = (rc < 0) ? 1: 0), out, "Unable to format event file name.");
    if ((fd = open(event_file_name, O_RDONLY)) == -1) {
        fail_on((rc = 1), out, "Unable to open event device");
    }
    fds[0].fd = fd;
    fds[0].events = POLLIN;

    rd = poll(fds, 1, -1);
    if (rd > 0 && (fds[0].revents & POLLIN)) {
        uint32_t events_user;
        rc = pread(fd, &events_user, sizeof(events_user), 0);
    }
    close(fd);

out:
    return rc;
}

/**
 * Write 4 identical buffers to the 4 different DRAM channels of the AFI
 */
int dma_example_hwsw_cosim(int slot_id, size_t buffer_size)
{
    const long input_size_per_frame = 3 * NUM_3D_TRI;
    const long output_size_per_frame = NUM_FB;
    const long num_of_frame = 100;
    const long total_input_size = input_size_per_frame * num_of_frame * sizeof(bit32);
    const long total_output_size = output_size_per_frame * num_of_frame * sizeof(bit32);

    int rc, pf_id = 0, bar_id = 0, fpga_attach_flags = 0;
    int device_num = 0;
    int write_fd, read_fd;
    FILE *ofile;
    bit8 frame_buffer_print[MAX_X][MAX_Y];
    bit32 *write_buffer = NULL, *read_buffer = NULL;
    uint32_t int_status_reg, control_reg;

    pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;
    rc = fpga_pci_get_dma_device_num(FPGA_DMA_XDMA, slot_id, &device_num);
    fail_on((rc = (rc != 0)? 1:0), out, "Unable to get xdma device number.");

    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags, &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);

    write_fd = -1;
    read_fd = -1;

    write_buffer = malloc(total_input_size);
    read_buffer = malloc(total_output_size);

    if (write_buffer == NULL || read_buffer == NULL) {
        rc = -ENOMEM;
        goto out;
    }

    printf("Memory has been allocated, initializing DMA and filling the buffer...\n");
#if !defined(SV_TEST)
    read_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ true);
    fail_on((rc = (read_fd < 0) ? -1 : 0), out, "unable to open read dma queue");

    write_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
        /*channel*/ 0, /*is_read*/ false);
    fail_on((rc = (write_fd < 0) ? -1 : 0), out, "unable to open write dma queue");
#else
    setup_send_rdbuf_to_c((uint8_t*)read_buffer, total_input_size);
    printf("Starting DDR init...\n");
    init_ddr();
    printf("Done DDR init...\n");
    rc = init_rr(0);
    fail_on(rc, out, "init rr failed");
    do_pre_rr();
    fail_on(is_replay(), out, "Skip application code, replaying");
#endif

    for (int k = 0; k < num_of_frame; k++) {
        for (int i = 0; i < NUM_3D_TRI; i++) {
            write_buffer[k*NUM_3D_TRI*3 + 3*i] =
                                    ((triangle_3ds[i].x0 & 0xff) << 0) |
                                    ((triangle_3ds[i].y0 & 0xff) << 8) |
                                    ((triangle_3ds[i].z0 & 0xff) << 16) |
                                    ((triangle_3ds[i].x1 & 0xff) << 24);
            write_buffer[k*NUM_3D_TRI*3 + 3*i + 1] =
                                    ((triangle_3ds[i].y1 & 0xff) << 0) |
                                    ((triangle_3ds[i].z1 & 0xff) << 8) |
                                    ((triangle_3ds[i].x2 & 0xff) << 16) |
                                    ((triangle_3ds[i].y2 & 0xff) << 24);
            write_buffer[k*NUM_3D_TRI*3 + 3*i + 2] = ((triangle_3ds[i].z2 & 0xff));
        }
    }

    rc = do_dma_write(write_fd, (uint8_t*)write_buffer, total_input_size, 0, 0, slot_id);
    fail_on(rc, out, "DMA write failed on DIMM 0");


    for (int i = 0; i < num_of_frame; i++) {
#ifdef SV_TEST
        cl_peek_ocl(0x00, &control_reg);
#else
        fpga_pci_peek(pci_bar_handle, 0x00, &control_reg);
#endif
        printf("%d: %d --> control status: %x\n", i, 0, control_reg);

        uint64_t input_addr = 0 + input_size_per_frame * sizeof(bit32) * i;
        uint64_t output_addr = MEM_16G + output_size_per_frame * sizeof(bit32) * i;

#ifdef SV_TEST
        cl_poke_ocl(0x04, 1); // Global Interrupt Enable
        cl_poke_ocl(0x08, 1); // Enable ap_done interrupt
        cl_poke_ocl(0x10, input_addr & 0xffffffff);
        cl_poke_ocl(0x14, (input_addr >> 32) & 0xffffffff);
        cl_poke_ocl(0x1c, output_addr & 0xffffffff);
        cl_poke_ocl(0x20, (output_addr >> 32) & 0xffffffff);
        cl_poke_ocl(0x00, 1);
#else
        fpga_pci_poke(pci_bar_handle, 0x04, 1); // Global Interrupt Enable
        fpga_pci_poke(pci_bar_handle, 0x08, 1); // Enable ap_done interrupt
        fpga_pci_poke(pci_bar_handle, 0x10, input_addr & 0xffffffff);
        fpga_pci_poke(pci_bar_handle, 0x14, (input_addr >> 32) & 0xffffffff);
        fpga_pci_poke(pci_bar_handle, 0x1c, output_addr & 0xffffffff);
        fpga_pci_poke(pci_bar_handle, 0x20, (output_addr >> 32) & 0xffffffff);
        fpga_pci_poke(pci_bar_handle, 0x00, 1);
#endif

#ifdef CSR_POLLING
        control_reg = 0;
        while ((control_reg & (1 << 1)) == 0) {
#ifdef SV_TEST
            cl_peek_ocl(0x00, &control_reg);
#else
            fpga_pci_peek(pci_bar_handle, 0x00, &control_reg);
#endif
            printf("%d: %d --> control status: %x\n", i, 0, control_reg);
#ifdef SV_TEST
            sv_pause(100);
#else
            usleep(100);
#endif
        }
#else /* CSR_POLLING */
        // This function would poll the 0th interrupt
        interrupt_polling(0);
#ifdef SV_TEST
        cl_peek_ocl(0x00, &control_reg);
#else
        fpga_pci_peek(pci_bar_handle, 0x00, &control_reg);
#endif
        printf("%d: %d --> control status: %x\n", i, 0, control_reg);
#endif /* CSR_POLLING */

#ifdef SV_TEST
        cl_peek_ocl(0x0c, &int_status_reg);
#else
        fpga_pci_peek(pci_bar_handle, 0x0c, &int_status_reg);
#endif
        printf("%d: interrupt status: %d\n", i, int_status_reg);

#ifdef SV_TEST
        cl_poke_ocl(0x00, 1 << 4); // make it continue
        cl_poke_ocl(0x0c, 1);
        cl_peek_ocl(0x0c, &int_status_reg);
#else
        fpga_pci_poke(pci_bar_handle, 0x00, 1 << 4); // make it continue
        fpga_pci_poke(pci_bar_handle, 0x0c, 1);
        fpga_pci_peek(pci_bar_handle, 0x0c, &int_status_reg);
#endif
        printf("%d: interrupt status: %d\n", i, int_status_reg);
    }

    rc = do_dma_read(read_fd, (uint8_t*)read_buffer, total_output_size, MEM_16G, 0, slot_id);
    fail_on(rc, out, "DMA read failed on DIMM 1");

    ofile = fopen("outputs.txt", "w+");

    for (int k = 0; k < num_of_frame; k++) {
      for (int i = 0, j = 0, n = 0; n < NUM_FB; n++) {
          bit32 temp = read_buffer[k * output_size_per_frame + n];
          frame_buffer_print[i][j++] = (temp >> 0) & 0xff;
          frame_buffer_print[i][j++] = (temp >> 8) & 0xff;
          frame_buffer_print[i][j++] = (temp >> 24) & 0xff;
          frame_buffer_print[i][j++] = (temp >> 16) & 0xff;
          if (j == MAX_Y) {
              i++;
              j = 0;
          }
      }

      for (int j = MAX_X - 1; j >= 0; j--) {
          for (int i = 0; i < MAX_Y; i++) {
              int pix;
              pix = frame_buffer_print[i][j];
              if (pix)
                  fprintf(ofile, "1");
              else
                  fprintf(ofile, "0");
          }
          fprintf(ofile, "\n");
      }
    }
    fclose(ofile);

    //bool passed = true;
    //for (dimm = 0; dimm < 4; dimm++) {
    //    rc = do_dma_read(read_fd, read_buffer, buffer_size,
    //        dimm * MEM_16G, dimm, slot_id);
    //    fail_on(rc, out, "DMA read failed on DIMM: %d", dimm);
    //    uint64_t differ = buffer_compare(read_buffer, write_buffer, buffer_size);
    //    if (differ != 0) {
    //        log_error("DIMM %d failed with %lu bytes which differ", dimm, differ);
    //        passed = false;
    //    } else {
    //        log_info("DIMM %d passed!", dimm);
    //    }
    //}
    //rc = (passed) ? 0 : 1;

out:
    if (write_buffer != NULL) {
        free(write_buffer);
    }
    if (read_buffer != NULL) {
        free(read_buffer);
    }
#if !defined(SV_TEST)
    if (write_fd >= 0) {
        close(write_fd);
    }
    if (read_fd >= 0) {
        close(read_fd);
    }
#endif
    do_post_rr();
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
