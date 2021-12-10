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

int hls_main(int argc, char **argv)
{
    size_t buffer_size;
#if defined(SV_TEST)
    buffer_size = 128;
#else
    buffer_size = 1ULL << 24;
#endif

    int rc = 0;
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

#endif

    rc = dma_example_hwsw_cosim(slot_id, buffer_size);
    fail_on(rc, out, "DMA example failed");

out:
    return rc;
}

void usage(const char* program_name) {
    printf("usage: %s [--slot <slot>]\n", program_name);
}

/**
 * Write 4 identical buffers to the 4 different DRAM channels of the AFI
 */
int dma_example_hwsw_cosim(int slot_id, size_t buffer_size)
{
    const long input_size_per_frame = 3 * NUM_3D_TRI;
    const long output_size_per_frame = NUM_FB;
#ifndef SV_TEST
    const long num_of_frame = 1000;
#else
    const long num_of_frame = 1;
#endif
    const long total_input_size = input_size_per_frame * num_of_frame * sizeof(bit32);
    const long total_output_size = output_size_per_frame * num_of_frame * sizeof(bit32);

    int rc = 0;
    FILE *ofile;
    bit8 frame_buffer_print[MAX_X][MAX_Y];
    bit32 *write_buffer = NULL, *read_buffer = NULL;
    uint32_t int_status_reg, control_reg;

    write_buffer = malloc(total_input_size);
    read_buffer = malloc(total_output_size);

    if (write_buffer == NULL || read_buffer == NULL) {
        rc = -ENOMEM;
        goto out;
    }

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

    rc = do_dma_write((uint8_t*)write_buffer, total_input_size, 0, 0, slot_id);
    fail_on(rc, out, "DMA write failed on DIMM 0");

    for (int i = 0; i < num_of_frame; i++) {
#ifdef DBG_CSR_LOG
        hls_peek_ocl(0x00, &control_reg);
        printf("%d: %d --> control status: %x\n", i, 0, control_reg);
#endif

        uint64_t input_addr = 0 + input_size_per_frame * sizeof(bit32) * i;
        uint64_t output_addr = MEM_16G + output_size_per_frame * sizeof(bit32) * i;

        hls_poke_ocl(0x04, 1); // Global Interrupt Enable
        hls_poke_ocl(0x08, 1); // Enable ap_done interrupt
        hls_poke_ocl(0x10, input_addr & 0xffffffff);
        hls_poke_ocl(0x14, (input_addr >> 32) & 0xffffffff);
        hls_poke_ocl(0x1c, output_addr & 0xffffffff);
        hls_poke_ocl(0x20, (output_addr >> 32) & 0xffffffff);
        hls_poke_ocl(0x00, 1);

#ifdef DBG_CSR_LOG
        printf("wait for completion at i=%d\n", i);
#endif
        hls_wait_task_complete(0x00);

#ifdef DBG_CSR_LOG
        hls_peek_ocl(0x0c, &int_status_reg);
        printf("%d: interrupt status: %d\n", i, int_status_reg);
#endif

        hls_poke_ocl(0x00, 1 << 4); // make it continue
        hls_poke_ocl(0x0c, 1);
#ifdef DBG_CSR_LOG
        hls_peek_ocl(0x0c, &int_status_reg);
        printf("%d: interrupt status: %d\n", i, int_status_reg);
#endif
    }

    rc = do_dma_read((uint8_t*)read_buffer, total_output_size, MEM_16G, 0, slot_id);
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
    /* if there is an error code, exit with status 1 */
    return (rc != 0 ? 1 : 0);
}

