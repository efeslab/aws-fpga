#include <stdlib.h>
#include <stdio.h>

#include "fpga_utils.h"
#include "cl_fpgarr.h"
#if defined(SV_TEST)
#include <fpga_pci_sv.h>
#include <utils/macros.h>
#else
#include <fpga_mgmt.h>
#include <fpga_pci.h>
# include <fpga_dma.h>
#include <utils/lcd.h>
#endif

static const uint16_t AMZ_PCI_VENDOR_ID = 0x1D0F; /* Amazon PCI Vendor ID */
static const uint16_t PCI_DEVICE_ID = 0xF001;
#define UINT64_HI32(x) ((((uint64_t) x) >> 32) & 0xffffffff)
#define UINT64_LO32(x) ( ((uint64_t) x) & 0xffffffff)
#define UINT64_FROM32(hi, lo) ((((uint64_t) hi) << 32) | ((uint64_t) lo))

#ifndef SV_TEST
/**
 * Checks to make sure that the slot has a recognized AFI loaded.
 */
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

int do_dma_read(struct _cl_context *cxt, void *host_buffer, size_t size,
                uint64_t address) {
#ifdef SV_TEST
    size_t transferred = 0;
    size_t step = 8192;
    while (transferred < size) {
        size_t curr_size = (size - transferred);
        if (curr_size > step) curr_size = step;
        sv_fpga_start_cl_to_buffer(cxt->slot_id, cxt->channel_id, curr_size,
                                   (uint64_t)host_buffer, address);
        transferred += step;
        host_buffer += step;
        address += step;
    }
    return 0;
#else
    return fpga_dma_burst_read(cxt->dma_read_fd, host_buffer, size, address);
#endif
}

int do_dma_write(struct _cl_context *cxt, const void *host_buffer, size_t size,
                 uint64_t address) {
#if defined(SV_TEST)
  size_t transferred = 0;
  size_t step = 8192;
  while (transferred < size) {
    size_t curr_size = (size - transferred);
    if (curr_size > step) curr_size = step;
    sv_fpga_start_buffer_to_cl(cxt->slot_id, cxt->channel_id, curr_size,
                               (uint64_t)host_buffer, address);
    transferred += step;
    host_buffer += step;
    address += step;
  }
  return 0;
#else
  return fpga_dma_burst_write(cxt->dma_write_fd, host_buffer, size, address);
#endif
}

void peek_ocl(struct _cl_context *cxt, uint64_t addr, uint32_t *data) {
#ifdef SV_TEST
    cl_peek_ocl(addr, data);
#else
    fpga_pci_peek(cxt->pci_bar_handle, addr, data);
#endif
}
void peek_ocl64(struct _cl_context *cxt, uint64_t addr, uint64_t *data) {
  uint32_t lo, hi;
  peek_ocl(cxt, addr, &lo);
  peek_ocl(cxt, addr + 4, &hi);
  *data = UINT64_FROM32(hi, lo);
}

void poke_ocl(struct _cl_context *cxt, uint64_t addr, uint32_t data) {
#ifdef SV_TEST
    cl_poke_ocl(addr, data);
#else
    fpga_pci_poke(cxt->pci_bar_handle, addr, data);
#endif
}
void poke_ocl64(struct _cl_context *cxt, uint64_t addr, uint64_t data) {
  poke_ocl(cxt, addr, UINT64_LO32(data));
  poke_ocl(cxt, addr + 4, UINT64_HI32(data));
}

void wait_task_complete() {
  rr_wait_irq(0);
}
