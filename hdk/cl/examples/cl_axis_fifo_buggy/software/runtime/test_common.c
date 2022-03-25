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
#include <pthread.h>
#include <assert.h>

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
#include <utils/log.h>


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
  #ifdef DBG_CSR_LOG
    hls_peek_ocl(ctl_reg_addr, &control_reg);
    printf("control status: %x\n", control_reg);
  #endif
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

#if !defined(SV_TEST)
/* use the stdout logger */
const struct logger *logger = &logger_stdout;
#else
# define log_error(...) printf(__VA_ARGS__); printf("\n")
# define log_info(...) printf(__VA_ARGS__); printf("\n")
#endif

int axis_fifo_main(int argc, char **argv);

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
#if defined(SV_TEST)
    int argc = 0;
    char *argv[2] = {"hls", NULL};
#endif

    int rc = 0;
    /* The statements within SCOPE ifdef below are needed for HW/SW
     * co-simulation with VCS */
#if defined(SCOPE)
    svScope scope;
    scope = svGetScopeFromName("tb");
    svSetScope(scope);
#endif

#if !defined(SV_TEST)
    /* setup logging to print to stdout */
    rc = log_init("test_hls");
    fail_on(rc, out, "Unable to initialize the log.");
    rc = log_attach(logger, NULL, 0);
    fail_on(rc, out, "%s", "Unable to attach to the log.");

    /* initialize the fpga_plat library */
    rc = fpga_mgmt_init();
    fail_on(rc, out, "Unable to initialize the fpga_mgmt library");
#endif

#if defined(SV_TEST)
    // Set up DDR in simulation
    printf("Starting DDR init...\n");
    init_ddr();
    printf("Done DDR init...\n");
#endif

    // Init RR
    rc = hls_init();
    fail_on(rc, out, "init hls failed");
    rc = init_rr(0);
    fail_on(rc, out, "init rr failed");
    do_pre_rr();
    fail_on(is_replay(), out, "Skip application code, replaying");

    // Call the main function of HLS application
    axis_fifo_main(argc, argv);

out:
    // Exit RR
    do_post_rr();
    hls_exit();

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

#ifdef SV_TEST
#define BUFFERSIZE (1LL << 15)
#else
#define BUFFERSIZE (1024*1024*128)
#endif
#define OCL_INJECT_CNT (65)
#define OCL_INJECT_SIZE (sizeof(uint32_t) * OCL_INJECT_CNT)
#define READBACK_SIZE (OCL_INJECT_SIZE + BUFFERSIZE)
#define REPORT_LIMIT (200)
#define BUFFER_ALIGNMENT (4096)
typedef enum {
  APP_CSR_DDR_WAIT_CYC = 0,
  APP_CSR_DONE,
  APP_CSR_INJECT,
  APP_CSR_ALLOW_DDR_W,
  APP_CSR_ALLOW_DDR_W_INTVL, // 0 is disable
} app_csr_idx_t;
#define APP_CSR_ADDR(idx) (0x4 * idx)
typedef struct {
  pthread_t tid;
} ocl_thread_info_t;
void *ocl_thread_start(void *);
int axis_fifo_main(int argc, char *argv[]) {
  // pcis_mem are all even
  uint32_t *pcis_mem = aligned_alloc(BUFFER_ALIGNMENT, BUFFERSIZE);
  fail_on(pcis_mem == NULL, out, "allocate pcis_mem failed");
  for (uint64_t i = 0; i < BUFFERSIZE/sizeof(uint32_t); ++i) {
    pcis_mem[i] = 2*i;
  }
  int rc;
  // ocl thread
  pthread_t ocl_tid;
  void *ocl_ret;
#ifdef SV_TEST
  ocl_thread_start(NULL);
  // force fifo to fill up to trigger the bug
  hls_poke_ocl(APP_CSR_ADDR(APP_CSR_ALLOW_DDR_W), 1);
  hls_poke_ocl(APP_CSR_ADDR(APP_CSR_DDR_WAIT_CYC), 10);
  //hls_poke_ocl(APP_CSR_ADDR(APP_CSR_ALLOW_DDR_W_INTVL), 4000);
#else
  // on real hardware, poke ocl in a new thread would trigger the bug
  hls_poke_ocl(APP_CSR_ADDR(APP_CSR_ALLOW_DDR_W), 1); //
  rc = pthread_create(&ocl_tid, NULL, &ocl_thread_start, NULL);
  fail_on(rc, out, "failed to create ocl pthread");
#endif
  // continue doing pcis dma write
  rc = do_dma_write((uint8_t*)pcis_mem, BUFFERSIZE, 0, 0, slot_id);
  fail_on(rc, out, "DMA write failed");
  // sync and notify the FPGA job is fully submitted
#ifdef SV_TEST
  // skip
#else
  pthread_join(ocl_tid, &ocl_ret);
#endif
  hls_poke_ocl(APP_CSR_ADDR(APP_CSR_DONE), 1);
  // wait for completion (irq)
  rr_wait_irq(0);
  // read back and check
  uint32_t *readback_mem = aligned_alloc(BUFFER_ALIGNMENT, READBACK_SIZE);
  fail_on(readback_mem == NULL, out, "allocate readback_mem failed");
  memset(readback_mem, 0, READBACK_SIZE);
  rc = do_dma_read((uint8_t*)readback_mem, READBACK_SIZE, 0, 0, slot_id);
  fail_on(rc, out, "DMA read failed");
  size_t unexpected = 0, minus1_counter = 0, oob_counter = 0;

  uint32_t *counters = aligned_alloc(BUFFER_ALIGNMENT, 2*BUFFERSIZE);
  for (size_t i = 0; i < 2*BUFFERSIZE/sizeof(uint32_t); ++i) {
    counters[i] = 0;
  }
  for (size_t i = 0; i < READBACK_SIZE/sizeof(uint32_t); ++i) {
    uint32_t n = readback_mem[i];
    printf("%d\n", n);
    if (0 <= n && n < 2*BUFFERSIZE/sizeof(uint32_t)) {
      counters[n]++;
    } else if (n == -1) {
      minus1_counter++;
    } else {
      oob_counter++;
    }
  }
  for (size_t i = 0; i < 2*BUFFERSIZE/sizeof(uint32_t); ++i) {
    if (i % 2) {
      // odd, from ocl
      if (i < 2 * OCL_INJECT_CNT + 1) {
        if (counters[i] != 1) {
          printf("ocl %d expected 1 got %d\n", i, counters[i]);
          unexpected++;
        }
      } else {
        continue;
      }
    } else {
      if (counters[i] != 1) {
        printf("pcis %d expected 1 got %d\n", i, counters[i]);
        unexpected++;
      }
    }
  }

  printf("total: %ld, unexpected: %ld places, -1: %ld places, oob: %ld places\n",
          BUFFERSIZE/sizeof(uint32_t) + OCL_INJECT_CNT, unexpected, minus1_counter, oob_counter);
  out:
  free(pcis_mem);
  free(readback_mem);
  return 0;
}
void *ocl_thread_start(void *arg) {
  // ocl are all odd
  for (size_t i = 0; i < OCL_INJECT_CNT; ++i) {
    hls_poke_ocl(APP_CSR_ADDR(APP_CSR_INJECT), 2 * i + 1);
  }
  return NULL;
}
