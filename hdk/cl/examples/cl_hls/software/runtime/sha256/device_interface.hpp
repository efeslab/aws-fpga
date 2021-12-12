#ifndef DEVICE_DEVICE_INTERFACE_HPP_
#define DEVICE_DEVICE_INTERFACE_HPP_

#include <vector>
#include "defs.hpp"


class DeviceInterface {
 public:
  DeviceInterface();
  struct chunk *run_fpga(int num_chunks, int active_buf);
  struct chunk *read_last_result(int active_buf);
  struct chunk *fetch_buffer(int active_buf);
  void unmap_last_result(int active_buf);
  ~DeviceInterface() = default;

 private:
  void *host_bufs[BUFFER_COUNT];
  uint64_t ocl_bufs[BUFFER_COUNT];
  int slot_id;
  bool is_first_task;
};

#endif  // DEVICE_DEVICE_INTERFACE_HPP_
