/*
 * Amazon FPGA Hardware Development Kit
 *
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Amazon Software License (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *    http://aws.amazon.com/asl/
 *
 * or in the "license" file accompanying this file. This file is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#pragma once

#include <stdio.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>
#include <malloc.h>
#include <poll.h>

#include <utils/sh_dpi_tasks.h>
#include "cl_fpgarr.h"

#ifdef SV_TEST
# include <fpga_pci_sv.h>
#else
# include <fpga_pci.h>
# include <fpga_mgmt.h>
# include "fpga_dma.h"
# include <utils/lcd.h>
#endif

/*
 * MACRO Configuration
 */
#undef CSR_POLLING
#define RR_IRQ_POLLING
#undef DBG_CSR_LOG
/**
 * Fills the buffer with bytes read from urandom.
 */
int fill_buffer_urandom(uint8_t *buf, size_t size);

/**
 * This function is like memcmp, but it returns the number of bytes that differ.
 *
 * @returns number of bytes which differ, i.e. zero if buffers are the same
 */
uint64_t buffer_compare(uint8_t *bufa, uint8_t *bufb,
    size_t buffer_size);

/**
 * Checks to make sure that the slot has a recognized AFI loaded.
 */
int check_slot_config(int slot_id);


extern int write_fd;
extern int read_fd;
extern int slot_id;
static inline int do_dma_read(uint8_t *buffer, size_t size,
    uint64_t address, int channel, int slot_id)
{
#if defined(SV_TEST)
    size_t transferred = 0;
    size_t step = 8192;
    while (transferred < size) {
        size_t curr_size = (size - transferred);
        if (curr_size > step) curr_size = step;
        sv_fpga_start_cl_to_buffer(slot_id, channel, curr_size, (uint64_t) buffer, address);
        transferred += step;
        buffer += step;
        address += step;
    }
    return 0;
#else
    return fpga_dma_burst_read(read_fd, buffer, size, address);
#endif
}

static inline int do_dma_write(uint8_t *buffer, size_t size,
    uint64_t address, int channel, int slot_id)
{
#if defined(SV_TEST)
    size_t transferred = 0;
    size_t step = 8192;
    while (transferred < size) {
        size_t curr_size = (size - transferred);
        if (curr_size > step) curr_size = step;
        sv_fpga_start_buffer_to_cl(slot_id, channel, curr_size, (uint64_t) buffer, address);
        transferred += step;
        buffer += step;
        address += step;
    }
    return 0;
#else
    return fpga_dma_burst_write(write_fd, buffer, size, address);
#endif
}

void hls_wait_task_complete(uint64_t ctl_reg_addr);
void hls_peek_ocl(uint64_t addr, uint32_t *data);
void hls_poke_ocl(uint64_t addr, uint32_t data);
static inline void hls_peek_ocl64(uint64_t addr, uint64_t *data) {
    uint32_t lo, hi;
    hls_peek_ocl(addr, &lo);
    hls_peek_ocl(addr + 4, &hi);
    *data = (hi << 32) | lo;
}
static inline void hls_poke_ocl64(uint64_t addr, uint64_t data) {
    hls_poke_ocl(addr, data & 0xffffffff);
    hls_poke_ocl(addr + 4, (data >> 32) & 0xffffffff);
}
void hls_wait(uint32_t unit);
int hls_interrupt_polling(int interrupt_number);

int hls_init();
void hls_exit();
