// device interface for connecting cpu to fpga using opencl code.
// initialization based on SDaccel hello world program

#include <string>
#include <vector>

#include "device_interface.hpp"
#include "defs.hpp"

extern "C" {
#include "test_common.h"
}

#define MEM_1G (1LL * 1024LL * 1024LL * 1024LL)

void check_error(int err) {
  if (err) {
    printf("ERROR: Operation Failed: %d\n", err);
    exit(EXIT_FAILURE);
  }
}

DeviceInterface::DeviceInterface() {
  for (int i = 0; i < BUFFER_COUNT; i++) {
    host_bufs[i] = aligned_alloc(4096, BUFFER_SIZE);
    ocl_bufs[i] = MEM_1G * i;
  }
  is_first_task = true;
  slot_id = 0;
  hls_poke_ocl(0x04, 1);
  hls_poke_ocl(0x08, 1);
  hls_poke_ocl(0x10, ocl_bufs[0] & 0xffffffff);
  hls_poke_ocl(0x14, (ocl_bufs[0] >> 32) & 0xffffffff);
  hls_poke_ocl(0x1c, ocl_bufs[1] & 0xffffffff);
  hls_poke_ocl(0x20, (ocl_bufs[1] >> 32) & 0xffffffff);
}

// used to bootstrap
struct chunk *DeviceInterface::fetch_buffer(int active_buf) {
  return (struct chunk *) host_bufs[active_buf];
}

struct chunk *DeviceInterface::run_fpga(int num_chunks, int active_buf) {
  int err;

  err = do_dma_write((uint8_t*)host_bufs[active_buf], BUFFER_SIZE, ocl_bufs[active_buf], 0, slot_id);
  check_error(err);

  if (!is_first_task) {
      hls_wait_task_complete(0x00);
      hls_poke_ocl(0x00, 1 << 4);
      hls_poke_ocl(0x0c, 1);
  } else {
      is_first_task = false;
  }

  hls_poke_ocl(0x28, num_chunks);
  hls_poke_ocl(0x30, active_buf);
  hls_poke_ocl(0x00, 1);

  err = do_dma_read((uint8_t*)host_bufs[1 - active_buf], BUFFER_SIZE, ocl_bufs[1 - active_buf], 0, slot_id);

  return (struct chunk *) host_bufs[1 - active_buf];
out:
  return 0;
}

struct chunk *DeviceInterface::read_last_result(int active_buf) {
  int err;

  hls_wait_task_complete(0x00);

  err = do_dma_read((uint8_t*)host_bufs[1 - active_buf], BUFFER_SIZE, ocl_bufs[1- active_buf], 0, slot_id);
  check_error(err);

  return (struct chunk *) host_bufs[1 - active_buf];
}

void DeviceInterface::unmap_last_result(int active_buf) {
    // do nothing
}
