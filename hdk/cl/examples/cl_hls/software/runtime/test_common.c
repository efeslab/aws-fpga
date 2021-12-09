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

#include <stdio.h>
#include <stdint.h>
#include <fcntl.h>
#include <errno.h>
#include <string.h>
#include <stdlib.h>
#include <unistd.h>

#include <sys/stat.h>
#include <sys/types.h>
#include <utils/sh_dpi_tasks.h>

#if defined(SV_TEST)
   #include <fpga_pci_sv.h>
   #include <utils/macros.h>
#else
   #include <fpga_pci.h>
   #include <fpga_mgmt.h>
   #include <utils/lcd.h>
#endif

#include "test_common.h"


static const uint16_t AMZ_PCI_VENDOR_ID = 0x1D0F; /* Amazon PCI Vendor ID */
static const uint16_t PCI_DEVICE_ID = 0xF001;

int fill_buffer_urandom(uint8_t *buf, size_t size)
{
    int fd, rc;

    fd = open("/dev/urandom", O_RDONLY);
    if (fd < 0) {
        return errno;
    }

    off_t i = 0;
    while ( i < size ) {
        rc = read(fd, buf + i, min(4096, size - i));
        if (rc < 0) {
            close(fd);
            return errno;
        }
        i += rc;
    }
    close(fd);

    return 0;
}

uint64_t buffer_compare(uint8_t *bufa, uint8_t *bufb,
    size_t buffer_size)
{
    size_t i;
    uint64_t differ = 0;
    for (i = 0; i < buffer_size; ++i) {
        
         if (bufa[i] != bufb[i]) {
            differ += 1;
        }
    }

    return differ;
}

#if !defined(SV_TEST)

int check_slot_config(int slot_id)
{
    int rc;
    struct fpga_mgmt_image_info info = {0};

    /* get local image description, contains status, vendor id, and device id */
    rc = fpga_mgmt_describe_local_image(slot_id, &info, 0);
    fail_on(rc, out, "Unable to get local image information. Are you running "
        "as root?");

    /* check to see if the slot is ready */
    if (info.status != FPGA_STATUS_LOADED) {
        rc = 1;
        fail_on(rc, out, "Slot %d is not ready", slot_id);
    }

    /* confirm that the AFI that we expect is in fact loaded */
    if (info.spec.map[FPGA_APP_PF].vendor_id != AMZ_PCI_VENDOR_ID ||
        info.spec.map[FPGA_APP_PF].device_id != PCI_DEVICE_ID)
    {
        rc = 1;
        char sdk_path_buf[512];
        char *sdk_env_var;
        sdk_env_var = getenv("SDK_DIR");
        snprintf(sdk_path_buf, sizeof(sdk_path_buf), "%s",
            (sdk_env_var != NULL) ? sdk_env_var : "<aws-fpga>");
        log_error(
            "...\n"
            "  The slot appears loaded, but the pci vendor or device ID doesn't match the\n"
            "  expected values. You may need to rescan the fpga with \n"
            "    fpga-describe-local-image -S %i -R\n"
            "  Note that rescanning can change which device file in /dev/ a FPGA will map to.\n",
            slot_id);
        log_error(
            "...\n"
            "  To remove and re-add your xdma driver and reset the device file mappings, run\n"
            "    sudo rmmod xdma && sudo insmod \"%s/sdk/linux_kernel_drivers/xdma/xdma.ko\"\n",
            sdk_path_buf);
        fail_on(rc, out, "The PCI vendor id and device of the loaded image are "
                         "not the expected values.");
    }

    char dbdf[16];
    snprintf(dbdf,
                  sizeof(dbdf),
                  PCI_DEV_FMT,
                  info.spec.map[FPGA_APP_PF].domain,
                  info.spec.map[FPGA_APP_PF].bus,
                  info.spec.map[FPGA_APP_PF].dev,
                  info.spec.map[FPGA_APP_PF].func);
    log_info("Operating on slot %d with id: %s", slot_id, dbdf);

out:
    return rc;
}
#endif


#if defined(SV_TEST)
static uint8_t *send_rdbuf_to_c_read_buffer = NULL;
static size_t send_rdbuf_to_c_buffer_size = 0;

void setup_send_rdbuf_to_c(uint8_t *read_buffer, size_t buffer_size)
{
    send_rdbuf_to_c_read_buffer = read_buffer;
    send_rdbuf_to_c_buffer_size = buffer_size;
}

int send_rdbuf_to_c(char* rd_buf)
{
#ifndef VIVADO_SIM
    /* Vivado does not support svGetScopeFromName */
    svScope scope;
    scope = svGetScopeFromName("tb");
    svSetScope(scope);
#endif
    int i;

    /* For Questa simulator the first 8 bytes are not transmitted correctly, so
     * the buffer is transferred with 8 extra bytes and those bytes are removed
     * here. Made this default for all the simulators. */
    for (i = 0; i < send_rdbuf_to_c_buffer_size; ++i) {
        send_rdbuf_to_c_read_buffer[i] = rd_buf[i+8];
    }

    /* end of line character is not transferered correctly. So assign that
     * here. */
    /*send_rdbuf_to_c_read_buffer[send_rdbuf_to_c_buffer_size - 1] = '\0';*/

    return 0;
}

#endif

void hls_wait_task_complete(uint64_t ctl_reg_addr) {
    uint32_t control_reg = 0;
#ifdef CSR_POLLING
    while ((control_reg & (1 << 1)) == 0) {
        hls_peek_ocl(ctl_reg_addr, &control_reg);
        printf("control status: %x\n", control_reg);
        hls_wait(100);
    }
#else // interrupt
#ifdef RR_IRQ_POLLING
    rr_wait_irq(0);
#else
    hls_interrupt_polling(0);
#endif
    hls_peek_ocl(ctl_reg_addr, &control_reg);
    printf("control status: %x\n", control_reg);
#endif
}

static pci_bar_handle_t pci_bar_handle = PCI_BAR_HANDLE_INIT;

void hls_peek_ocl(uint64_t addr, uint32_t *data) {
#ifdef SV_TEST
    cl_peek_ocl(addr, data);
#else
    fpga_pci_peek(pci_bar_handle, addr, data);
#endif
}

void hls_poke_ocl(uint64_t addr, uint32_t data) {
#ifdef SV_TEST
    cl_poke_ocl(addr, data);
#else
    fpga_pci_poke(pci_bar_handle, addr, data);
#endif
}

void hls_wait(uint32_t unit) {
#ifdef SV_TEST
    sv_pause(unit);
#else
    usleep(unit);
#endif
}

int write_fd = -1;
int read_fd = -1;
int slot_id = 0;

int hls_init() {
    int rc = 0;
    int pf_id = 0, bar_id = 0, fpga_attach_flags = 0;
    int device_num = 0;
    errno = 0;
#ifndef SV_TEST
    rc = fpga_pci_get_dma_device_num(FPGA_DMA_XDMA, slot_id, &device_num);
    fail_on((rc = (rc != 0) ? 1 : 0), out, "Unable to get xdma device number.");

    rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags,
                         &pci_bar_handle);
    fail_on(rc, out, "Unable to attach to the AFI on slot id %d", slot_id);
    read_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
                                  /*channel*/ 0, /*is_read*/ true);
    fail_on((rc = (read_fd < 0) ? -1 : 0), out,
            "unable to open read dma queue");

    write_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
                                   /*channel*/ 0, /*is_read*/ false);
    fail_on((rc = (write_fd < 0) ? -1 : 0), out,
            "unable to open write dma queue");
    check_slot_config(slot_id);
out:
#endif
    return rc;
}

void hls_exit() {
#ifndef SV_TEST
    if (write_fd >= 0) {
        close(write_fd);
    }
    if (read_fd >= 0) {
        close(read_fd);
    }
#endif
}

int hls_interrupt_polling(int interrupt_number) {
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