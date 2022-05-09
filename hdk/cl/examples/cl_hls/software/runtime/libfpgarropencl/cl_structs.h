#ifndef LIBFPGARROPENCL_CL_STRUCTS_H
#define LIBFPGARROPENCL_CL_STRUCTS_H
#define CL_TARGET_OPENCL_VERSION 220
#include <CL/opencl.h>
#ifdef SV_TEST
#include <fpga_pci_sv.h>
#else
#include <fpga_pci.h>
#endif

#include "fpgarropencl.h"
struct _cl_context {
  int global_used;
  int slot_id;
#ifdef SV_TEST
  int channel_id;
#else
  int dma_read_fd;
  int dma_write_fd;
  pci_bar_handle_t pci_bar_handle;
#endif
  cl_uint num_devs;
  cl_device_id *devs;
  cl_int refcnt;
};

struct _cl_mem {
  cl_int refcnt;
  uint64_t fpga_ddr_addr;
  size_t size;
};

#define NAME_MAX_LEN (128)
struct _cl_platform_id {
  const char name[NAME_MAX_LEN];
  const char vendor[NAME_MAX_LEN];
  const char profile[NAME_MAX_LEN];
  const char version[NAME_MAX_LEN];
};
struct _cl_device_id {
  cl_int refcnt;
};

#define MAX_DEV_PER_PROG 4
struct _cl_program {
  cl_int refcnt;
  cl_context cxt;
  fake_program_spec_t spec;
  cl_uint num_devs;
  cl_device_id devs[MAX_DEV_PER_PROG];
};

struct _cl_kernel {
  cl_int refcnt;
  char name[NAME_MAX_LEN];
  cl_program prog;
  void *args_value[FPGARR_OPENCL_KERNEL_MAX_ARGS];
  size_t args_size[FPGARR_OPENCL_KERNEL_MAX_ARGS];
};

struct _cl_command_queue {
  cl_int refcnt;
  // commands is a double linked list of cl_event pointers that points to the
  // event associated with each command. cl_event embeds everything I want to
  // know about a command.
  cl_event cmdheader;
  cl_uint qsize; // queue size, not used
  cl_context cxt;
  uint8_t enableProfiling;
};

struct _cl_event {
  cl_int refcnt;
  // double linked list
  cl_event prev; // the last event in the list
  cl_event next; // the first event in the list
  cl_command_queue cmdq;
  cl_int status;
  cl_command_type t;
  union {
    struct {
      void *host_ptr;
      cl_mem mem;
      size_t offset;
      size_t size;
    } argReadBuf;
    struct {
      const void *host_ptr;
      cl_mem mem;
      size_t offset;
      size_t size;
    } argWriteBuf;
    struct {
      cl_kernel k;
    } argKernel;
  };
  struct {
    cl_ulong ts_queued;
    cl_ulong ts_submit;
    cl_ulong ts_start;
    cl_ulong ts_end;
  } profiling_info;
  cl_uint num_events_in_wait_list;
  cl_event *event_wait_list;
};
// enqueue a cl_event into its corresponding command queue
extern void enqueue_cl_event(cl_event event);
// allocate a new cl_event that are bounds to a given command queue. but does
// not enqueue
extern cl_event alloc_cl_event(cl_command_queue cmdq);
extern void linked_list_remove_cl_event(cl_event event);
extern cl_int cl_command_exec(cl_event event);
#endif  // LIBFPGARROPENCL_CL_STRUCTS_H
