#define CL_TARGET_OPENCL_VERSION 220
#include <CL/cl_ext_xilinx.h>
#include <CL/opencl.h>
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

// headers to deal with vendor lib
#ifdef SV_TEST
#include <fpga_pci_sv.h>
#include <utils/sh_dpi_tasks.h>
#else
#include <fpga_dma.h>
#include <fpga_mgmt.h>
#include <fpga_pci.h>
#include <utils/lcd.h>
#endif

// headers from current lib
#include "cl_fpgarr.h"
#include "cl_structs.h"
#include "fpga_mem_mgr.h"
#include "fpga_utils.h"

struct _cl_device_id g_devid;
cl_device_id g_cl_cxt_devs[] = {
  &g_devid,
};
struct _cl_context g_cl_cxt = {
    .global_used = 0,
    .slot_id = 0,
#ifndef SV_TEST
    .pci_bar_handle = PCI_BAR_HANDLE_INIT,
#endif
    .num_devs = sizeof(g_cl_cxt_devs)/sizeof(g_cl_cxt_devs[0]),
    .devs = g_cl_cxt_devs,
    .refcnt = 0,
};

#define CL_GET_INFO(type, retvalue) \
  CL_GET_INFO_WITH_SIZE(type, retvalue, sizeof(type))
#define CL_GET_INFO_WITH_SIZE(type, retvalue, retsize)            \
  if (param_value) {                                              \
    if (param_value_size < sizeof(type)) return CL_INVALID_VALUE; \
    *((type *)param_value) = retvalue;                            \
  }                                                               \
  if (param_value_size_ret) *param_value_size_ret = retsize
#define CL_GET_INFO_MEMCPY(retptr, retsize)                  \
  if (param_value) {                                         \
    if (param_value_size < retsize) return CL_INVALID_VALUE; \
    memcpy(param_value, retptr, retsize);                    \
  }                                                          \
  if (param_value_size_ret) *param_value_size_ret = retsize
cl_context clCreateContext(
    const cl_context_properties *properties, cl_uint num_devices,
    const cl_device_id *devices,
    void(CL_CALLBACK *pfn_notify)(const char *errinfo, const void *private_info,
                                  size_t cb, void *user_data),
    void *user_data, cl_int *errcode_ret) {
  int rc;
  fail_on_errret(g_cl_cxt.global_used, err, CL_OUT_OF_RESOURCES,
                 "global context is used");
  g_cl_cxt.global_used = 1;
#ifdef SV_TEST
  g_cl_cxt.channel_id = 0;
#else   // SV_TEST
  int pf_id = 0;
  int bar_id = 0;  // bar_id == 0 means the OCL AXIL interface
  int fpga_attach_flags = 0;
  int device_num = 0;
  int slot_id = g_cl_cxt.slot_id;
  rc = fpga_pci_get_dma_device_num(FPGA_DMA_XDMA, slot_id, &device_num);
  fail_on_errret(rc, err, CL_OUT_OF_RESOURCES,
                 "Unable to get xdma device number.");

  rc = fpga_pci_attach(slot_id, pf_id, bar_id, fpga_attach_flags,
                       &(g_cl_cxt.pci_bar_handle));
  fail_on_errret(rc, err, CL_OUT_OF_RESOURCES,
                 "Unable to attach to the AFI on slot id %d", slot_id);
  g_cl_cxt.dma_read_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
                                             /*channel*/ 0, /*is_read*/ true);
  rc = (g_cl_cxt.dma_read_fd < 0) ? -1 : 0;
  fail_on_errret(rc, err, CL_OUT_OF_RESOURCES, "unable to open read dma queue");

  g_cl_cxt.dma_write_fd = fpga_dma_open_queue(FPGA_DMA_XDMA, slot_id,
                                              /*channel*/ 0, /*is_read*/ false);
  rc = (g_cl_cxt.dma_write_fd < 0) ? -1 : 0;
  fail_on_errret(rc, err, CL_OUT_OF_RESOURCES,
                 "unable to open write dma queue");
  check_slot_config(slot_id);
#endif  // SV_TEST
  errcode_is(CL_SUCCESS);
  return &g_cl_cxt;

err:
  return NULL;
}

cl_int clRetainContext(cl_context context) {
  if (context != &g_cl_cxt)
    return CL_INVALID_CONTEXT;
  else {
    g_cl_cxt.refcnt++;
    return CL_SUCCESS;
  }
}

cl_int clReleaseContext(cl_context context) {
  if (context != &g_cl_cxt)
    return CL_INVALID_CONTEXT;
  else {
    context->refcnt--;
    if (g_cl_cxt.refcnt == 0) {
      context->global_used = 0;
#ifndef SV_TEST
      assert(fpga_pci_detach(context->pci_bar_handle) == 0);
      close(context->dma_read_fd);
      close(context->dma_write_fd);
#endif
    }
    return CL_SUCCESS;
  }
}

cl_mem clCreateBuffer(cl_context context, cl_mem_flags flags, size_t size,
                      void *host_ptr, cl_int *errcode_ret) {
  if (flags & (CL_MEM_USE_HOST_PTR | CL_MEM_ALLOC_HOST_PTR)) {
    errcode_is(CL_INVALID_VALUE);
    return NULL;
  }
  if ((flags & CL_MEM_COPY_HOST_PTR) && !host_ptr) {
    errcode_is(CL_INVALID_HOST_PTR);
    return NULL;
  }
  if (size == 0) {
    errcode_is(CL_INVALID_BUFFER_SIZE);
    return NULL;
  }

  cl_mem ret = (struct _cl_mem *)malloc(sizeof(struct _cl_mem));
  if (!ret) {
    errcode_is(CL_OUT_OF_HOST_MEMORY);
    return NULL;
  }
  ret->size = size;
  ret->refcnt = 1;

  if (flags & CL_MEM_EXT_PTR_XILINX) {
    cl_mem_ext_ptr_t *ext_p = (cl_mem_ext_ptr_t *)(host_ptr);
    if ((ext_p->flags & XCL_MEM_DDR_BANK0) ||
        (ext_p->banks & XCL_MEM_DDR_BANK0)) {
      if (fpga_alloc_bank(0, size, &(ret->fpga_ddr_addr)) != 0) goto err_oom;
    } else if ((ext_p->flags & XCL_MEM_DDR_BANK1) ||
               (ext_p->banks & XCL_MEM_DDR_BANK1)) {
      if (fpga_alloc_bank(1, size, &(ret->fpga_ddr_addr)) != 0) goto err_oom;
    } else if ((ext_p->flags & XCL_MEM_DDR_BANK2) ||
               (ext_p->banks & XCL_MEM_DDR_BANK2)) {
      if (fpga_alloc_bank(2, size, &(ret->fpga_ddr_addr)) != 0) goto err_oom;
    } else if ((ext_p->flags & XCL_MEM_DDR_BANK3) ||
               (ext_p->banks & XCL_MEM_DDR_BANK3)) {
      if (fpga_alloc_bank(3, size, &(ret->fpga_ddr_addr)) != 0) goto err_oom;
    }
  } else {
    if (fpga_alloc(size, &(ret->fpga_ddr_addr)) != 0) goto err_oom;
  }
  if (flags & CL_MEM_COPY_HOST_PTR) {
    int rc = do_dma_write(context, host_ptr, size, ret->fpga_ddr_addr);
    fail_on_errret(rc, err, CL_MEM_OBJECT_ALLOCATION_FAILURE,
                   "createBuffer dma_write copy host failed");
  }
  errcode_is(CL_SUCCESS);
  return ret;
err_oom:
  errcode_is(CL_OUT_OF_RESOURCES);
err:
  free(ret);
  return NULL;
}

cl_int clRetainMemObject(cl_mem memobj) {
  memobj->refcnt++;
  return CL_SUCCESS;
}

cl_int clReleaseMemObject(cl_mem memobj) {
  assert(memobj->refcnt > 0);
  memobj->refcnt--;
  if (!memobj->refcnt) {
    free(memobj);
  }
  return CL_SUCCESS;
}

#ifdef SV_TEST
struct _cl_platform_id g_platid = {
    .name = "CLFPGARR OpenCL Fake Wrapper (For simulation)",
    .vendor = "CLFPGARR",
    .profile = "Simulation",
    .version = "1.0"};
#else
struct _cl_platform_id g_platid = {
    .name = "CLFPGARR OpenCL Fake Wrapper (For real hardware)",
    .vendor = "CLFPGARR",
    .profile = "RealHardware",
    .version = "1.0"};
#endif
cl_int clGetPlatformIDs(cl_uint num_entries, cl_platform_id *platforms,
                        cl_uint *num_platforms) {
  if (num_entries >= 1) platforms[0] = &g_platid;
  if (num_platforms) *num_platforms = 1;
  return CL_SUCCESS;
}

cl_int clGetPlatformInfo(cl_platform_id platform, cl_platform_info param_name,
                         size_t param_value_size, void *param_value,
                         size_t *param_value_size_ret) {
  if (platform == NULL)
    platform = &g_platid;
  else if (platform != &g_platid)
    return CL_INVALID_PLATFORM;
  if (param_value_size < 4) return CL_INVALID_VALUE;
  size_t out_size = 0;
  switch (param_name) {
    case CL_PLATFORM_PROFILE:
      out_size = min(strlen(platform->profile) + 1, param_value_size);
      strncpy(param_value, platform->profile, out_size);
      if (param_value_size_ret) *param_value_size_ret = out_size;
      break;
    case CL_PLATFORM_VERSION:
      out_size = min(strlen(platform->version) + 1, param_value_size);
      strncpy(param_value, platform->version, out_size);
      if (param_value_size_ret) *param_value_size_ret = out_size;
      break;
    case CL_PLATFORM_NAME:
      out_size = min(strlen(platform->name) + 1, param_value_size);
      strncpy(param_value, platform->name, out_size);
      if (param_value_size_ret) *param_value_size_ret = out_size;
      break;
    case CL_PLATFORM_VENDOR:
      out_size = min(strlen(platform->vendor) + 1, param_value_size);
      strncpy(param_value, platform->vendor, out_size);
      if (param_value_size_ret) *param_value_size_ret = out_size;
      break;
    default:
      return CL_INVALID_VALUE;
  }
  return CL_SUCCESS;
}

struct _cl_device_id g_devid = {.refcnt = 0};
cl_int clGetDeviceIDs(cl_platform_id platform, cl_device_type device_type,
                      cl_uint num_entries, cl_device_id *devices,
                      cl_uint *num_devices) {
  if (platform != NULL && platform != &g_platid) return CL_INVALID_PLATFORM;
  if (device_type == CL_DEVICE_TYPE_CPU || device_type == CL_DEVICE_TYPE_GPU)
    return CL_INVALID_DEVICE_TYPE;
  if (num_entries >= 1) devices[0] = &g_devid;
  if (num_devices) *num_devices = 1;
  return CL_SUCCESS;
}
cl_int clRetainDevice(cl_device_id device) {
  if (device != &g_devid)
    return CL_INVALID_DEVICE;
  else {
    g_devid.refcnt++;
    return CL_SUCCESS;
  }
}
cl_int clReleaseDevice(cl_device_id device) {
  if (device != &g_devid)
    return CL_INVALID_DEVICE;
  else {
    g_devid.refcnt--;
    return CL_SUCCESS;
  }
}

cl_int clGetDeviceInfo(cl_device_id device, cl_device_info param_name,
                       size_t param_value_size, void *param_value,
                       size_t *param_value_size_ret) {
  // not implemented
  return CL_INVALID_VALUE;
}

cl_program clCreateProgramWithBinary(cl_context context, cl_uint num_devices,
                                     const cl_device_id *device_list,
                                     const size_t *lengths,
                                     const unsigned char **binaries,
                                     cl_int *binary_status,
                                     cl_int *errcode_ret) {
  if (num_devices != 1) {
    errcode_is(CL_INVALID_VALUE);
    return NULL;
  }
  if (device_list == NULL || lengths == NULL || binaries == NULL) {
    errcode_is(CL_INVALID_VALUE);
    return NULL;
  }
  if (num_devices > MAX_DEV_PER_PROG) {
    errcode_is(CL_INVALID_VALUE);
    return NULL;
  }
  if (device_list[0] != &g_devid) {
    errcode_is(CL_INVALID_DEVICE);
    return NULL;
  }
  if (lengths[0] == 0 || binaries[0] == NULL) {
    errcode_is(CL_INVALID_VALUE);
    return NULL;
  }
  cl_program prog = (cl_program)malloc(sizeof(struct _cl_program));
  prog->cxt = context;
  clRetainContext(context);
  prog->refcnt = 1;
  prog->spec = *((fake_program_spec_t *)binaries[0]);
  prog->num_devs = num_devices;
  memset(prog->devs, 0, sizeof(prog->devs));
  for (cl_uint i = 0; i < num_devices; ++i) {
    prog->devs[i] = device_list[i];
    clRetainDevice(prog->devs[i]);
  }
  errcode_is(CL_SUCCESS);
  return prog;
}
cl_int clRetainProgram(cl_program program) {
  ++program->refcnt;
  return CL_SUCCESS;
}
cl_int clReleaseProgram(cl_program program) {
  assert(program->refcnt > 0);
  program->refcnt--;
  if (!program->refcnt) {
    clReleaseContext(program->cxt);
    for (cl_uint i = 0; i < program->num_devs; ++i) {
      clReleaseDevice(program->devs[i]);
    }
    free(program);
  }
  return CL_SUCCESS;
}

cl_int clBuildProgram(cl_program program, cl_uint num_devices,
                      const cl_device_id *device_list, const char *options,
                      void(CL_CALLBACK *pfn_notify)(cl_program program,
                                                    void *user_data),
                      void *user_data) {
  if (num_devices) return CL_INVALID_VALUE;
  return CL_SUCCESS;
}

cl_int clGetProgramBuildInfo(cl_program program, cl_device_id device,
                             cl_program_build_info param_name,
                             size_t param_value_size, void *param_value,
                             size_t *param_value_size_ret) {
  if (device != &g_devid) return CL_INVALID_DEVICE;
  if (param_value_size < 4) return CL_INVALID_VALUE;
  size_t out_size = 0;
  switch (param_name) {
    case CL_PROGRAM_BUILD_STATUS:
      *((cl_build_status *)param_value) = CL_BUILD_SUCCESS;
      if (param_value_size_ret) *param_value_size_ret = sizeof(cl_build_status);
      break;
    case CL_PROGRAM_BUILD_LOG:
    case CL_PROGRAM_BUILD_OPTIONS:
      out_size = min(strlen("N/A") + 1, param_value_size);
      strncpy(param_value, "N/A", out_size);
      if (param_value_size_ret) *param_value_size_ret = out_size;
      break;
    default:
      return CL_INVALID_VALUE;
  }
  return CL_SUCCESS;
}

cl_int clGetProgramInfo(cl_program program, cl_program_info param_name,
                        size_t param_value_size, void *param_value,
                        size_t *param_value_size_ret) {
  static char empty_prog_src[] = "";
  static char fake_kernel_names[] = "FPGARR_INTERCEPTED_KERNEL";
  if (!program) return CL_INVALID_PROGRAM;
  switch (param_name) {
    case CL_PROGRAM_REFERENCE_COUNT:
      CL_GET_INFO(cl_uint, program->refcnt);
      break;
    case CL_PROGRAM_CONTEXT:
      CL_GET_INFO(cl_context, program->cxt);
      break;
    case CL_PROGRAM_NUM_DEVICES:
      CL_GET_INFO(cl_uint, program->num_devs);
      break;
    case CL_PROGRAM_DEVICES:
      CL_GET_INFO_MEMCPY(program->devs, sizeof(cl_device_id) * program->num_devs);
      break;
    case CL_PROGRAM_SOURCE:
    case CL_PROGRAM_IL:
      CL_GET_INFO_MEMCPY(empty_prog_src, sizeof(empty_prog_src));
      break;
    case CL_PROGRAM_NUM_KERNELS:
      CL_GET_INFO(size_t, 1);
      break;
    case CL_PROGRAM_KERNEL_NAMES:
      CL_GET_INFO_MEMCPY(fake_kernel_names, sizeof(fake_kernel_names));
      break;
    default:
      return CL_INVALID_VALUE;
  }
  return CL_SUCCESS;
}
cl_kernel clCreateKernel(cl_program program, const char *kernel_name,
                         cl_int *errcode_ret) {
  cl_kernel k = (cl_kernel)malloc(sizeof(struct _cl_kernel));
  k->refcnt = 1;
  strncpy(k->name, kernel_name, NAME_MAX_LEN);
  k->prog = program;
  memset(k->args_value, 0, sizeof(k->args_value));
  memset(k->args_size, 0, sizeof(k->args_size));
  errcode_is(CL_SUCCESS);
  return k;
}
cl_int clRetainKernel(cl_kernel kernel) {
  ++kernel->refcnt;
  return CL_SUCCESS;
}
cl_int clReleaseKernel(cl_kernel kernel) {
  assert(kernel->refcnt > 0);
  --kernel->refcnt;
  if (!kernel->refcnt) {
    for (int i = 0; i < FPGARR_OPENCL_KERNEL_MAX_ARGS; ++i) {
      if (kernel->args_value[i]) free(kernel->args_value[i]);
    }
    free(kernel);
  }
  return CL_SUCCESS;
}

cl_command_queue clCreateCommandQueueWithProperties(
    cl_context context, cl_device_id device,
    const cl_queue_properties *properties, cl_int *errcode_ret) {
  if (context != &g_cl_cxt) {
    errcode_is(CL_INVALID_CONTEXT);
    return NULL;
  }
  if (device != &g_devid) {
    errcode_is(CL_INVALID_DEVICE);
    return NULL;
  }
  uint8_t enableProfiling = 0;
  size_t queue_size = 0;
  const cl_queue_properties *prop = properties;
  while (prop != NULL && (*prop != 0)) {
    const cl_queue_properties *val = prop + 1;
    if (val == NULL) {
      errcode_is(CL_INVALID_QUEUE_PROPERTIES);
      return NULL;
    }
    switch (*prop) {
      case CL_QUEUE_PROPERTIES: {
        cl_bitfield bf = *((const cl_bitfield *)(val));
        if (bf & CL_QUEUE_PROFILING_ENABLE) enableProfiling = 1;
        break;
      }
#ifdef CL_VERSION_2_0
      case CL_QUEUE_SIZE:
        queue_size = *((const cl_uint *)val);
        break;
#endif
      default:
        errcode_is(CL_INVALID_QUEUE_PROPERTIES);
        return NULL;
    }
    prop += 2;
  }
  cl_command_queue cmdq =
      (cl_command_queue)malloc(sizeof(struct _cl_command_queue));
  if (cmdq) {
    cmdq->refcnt = 1;
    cmdq->qsize = queue_size;
    cmdq->cxt = context;
    cmdq->enableProfiling = enableProfiling;
    cl_event cmdheader = (cl_event)malloc(sizeof(struct _cl_event));
    if (cmdheader) {
      cmdq->cmdheader = cmdheader;
      cmdheader->refcnt = 3;  // one from cmdqueue, two from itself
      cmdheader->prev = cmdheader;
      cmdheader->next = cmdheader;
      cmdheader->status = CL_COMPLETE;
      cmdheader->t = 0xffff;
      cmdheader->num_events_in_wait_list = 0;
      cmdheader->event_wait_list = NULL;
    } else
      goto err_oom_cmdheader;
    errcode_is(CL_SUCCESS);
    return cmdq;
  } else
    goto err_oom_cmdq;
err_oom_cmdheader:
  free(cmdq);
err_oom_cmdq:
  errcode_is(CL_OUT_OF_HOST_MEMORY);
  return NULL;
}
CL_EXT_PREFIX__VERSION_1_2_DEPRECATED cl_command_queue clCreateCommandQueue(
    cl_context context, cl_device_id device,
    cl_command_queue_properties properties,
    cl_int *errcode_ret) CL_EXT_SUFFIX__VERSION_1_2_DEPRECATED {
  cl_command_queue_properties prop_array[] = {
      CL_QUEUE_PROPERTIES, properties,
      0  // 0 terminated
  };
  return clCreateCommandQueueWithProperties(context, device, prop_array,
                                            errcode_ret);
}
cl_int clRetainCommandQueue(cl_command_queue command_queue) {
  command_queue->refcnt++;
  return CL_SUCCESS;
}

cl_int clReleaseCommandQueue(cl_command_queue command_queue) {
  assert(command_queue->refcnt > 0);
  command_queue->refcnt--;
  if (!command_queue->refcnt) {
    // remove ref from this header's prev and next
    linked_list_remove_cl_event(command_queue->cmdheader);
    // remove ref from cmdq to this header
    clReleaseEvent(command_queue->cmdheader);
    free(command_queue);
  }
  return CL_SUCCESS;
}

cl_int clEnqueueReadBuffer(cl_command_queue command_queue, cl_mem buffer,
                           cl_bool blocking_read, size_t offset, size_t size,
                           void *ptr, cl_uint num_events_in_wait_list,
                           const cl_event *event_wait_list, cl_event *event) {
  cl_event newev = alloc_cl_event(command_queue);
  newev->t = CL_COMMAND_READ_BUFFER;
  newev->argReadBuf.host_ptr = ptr;
  newev->argReadBuf.offset = offset;
  newev->argReadBuf.size = size;
  newev->argReadBuf.mem = buffer;
  clRetainMemObject(buffer);
  if (num_events_in_wait_list) {
    if (!event_wait_list) return CL_INVALID_EVENT_WAIT_LIST;
    newev->num_events_in_wait_list = num_events_in_wait_list;
    newev->event_wait_list =
        (cl_event *)malloc(sizeof(cl_event) * num_events_in_wait_list);
    if (!newev->event_wait_list) return CL_OUT_OF_HOST_MEMORY;
    memcpy(newev->event_wait_list, event_wait_list,
           sizeof(cl_event) * num_events_in_wait_list);
    for (cl_uint i = 0; i < num_events_in_wait_list; ++i)
      clRetainEvent(event_wait_list[i]);
  }
  cl_int ret;
  if (blocking_read == CL_TRUE) {
    ret = cl_command_exec(newev);
  } else {
    newev->status = CL_QUEUED;
    enqueue_cl_event(newev);
    ret = CL_SUCCESS;
  }
  if (event) {
    *event = newev;
    clRetainEvent(newev);
  }
  return ret;
}

cl_int clEnqueueWriteBuffer(cl_command_queue command_queue, cl_mem buffer,
                            cl_bool blocking_write, size_t offset, size_t size,
                            const void *ptr, cl_uint num_events_in_wait_list,
                            const cl_event *event_wait_list, cl_event *event) {
  cl_event newev = alloc_cl_event(command_queue);
  newev->t = CL_COMMAND_WRITE_BUFFER;
  newev->argWriteBuf.host_ptr = ptr;
  newev->argWriteBuf.offset = offset;
  newev->argWriteBuf.size = size;
  newev->argWriteBuf.mem = buffer;
  clRetainMemObject(buffer);
  if (num_events_in_wait_list) {
    if (!event_wait_list) return CL_INVALID_EVENT_WAIT_LIST;
    newev->num_events_in_wait_list = num_events_in_wait_list;
    newev->event_wait_list =
        (cl_event *)malloc(sizeof(cl_event) * num_events_in_wait_list);
    if (!newev->event_wait_list) return CL_OUT_OF_HOST_MEMORY;
    memcpy(newev->event_wait_list, event_wait_list,
           sizeof(cl_event) * num_events_in_wait_list);
    for (cl_uint i = 0; i < num_events_in_wait_list; ++i)
      clRetainEvent(event_wait_list[i]);
  }
  cl_int ret;
  if (blocking_write == CL_TRUE) {
    ret = cl_command_exec(newev);
  } else {
    newev->status = CL_QUEUED;
    enqueue_cl_event(newev);
    ret = CL_SUCCESS;
  }
  if (event) {
    *event = newev;
    clRetainEvent(newev);
  }
  return ret;
}

cl_int clEnqueueTask(cl_command_queue command_queue, cl_kernel kernel,
                     cl_uint num_events_in_wait_list,
                     const cl_event *event_wait_list, cl_event *event) {
  cl_event newev = alloc_cl_event(command_queue);
  newev->status = CL_QUEUED;
  newev->t = CL_COMMAND_NDRANGE_KERNEL;
  newev->argKernel.k = kernel;
  clRetainKernel(kernel);
  if (num_events_in_wait_list) {
    if (!event_wait_list) return CL_INVALID_EVENT_WAIT_LIST;
    newev->event_wait_list =
        (cl_event *)malloc(sizeof(cl_event) * num_events_in_wait_list);
    if (!newev->event_wait_list) return CL_OUT_OF_HOST_MEMORY;
    memcpy(newev->event_wait_list, event_wait_list,
           sizeof(cl_event) * num_events_in_wait_list);
    for (cl_uint i = 0; i < num_events_in_wait_list; ++i)
      clRetainEvent(event_wait_list[i]);
  }
  if (event) {
    *event = newev;
    clRetainEvent(newev);
  }
  return CL_SUCCESS;
}

cl_int clEnqueueNDRangeKernel(
    cl_command_queue command_queue, cl_kernel kernel, cl_uint work_dim,
    const size_t *global_work_offset, const size_t *global_work_size,
    const size_t *local_work_size, cl_uint num_events_in_wait_list,
    const cl_event *event_wait_list, cl_event *event) {
  if (work_dim != 1) return CL_INVALID_WORK_DIMENSION;
  if (global_work_offset != NULL) return CL_INVALID_GLOBAL_OFFSET;
  if (global_work_size[0] != 1) return CL_INVALID_GLOBAL_WORK_SIZE;
  if (local_work_size != NULL && (*local_work_size != 1))
    return CL_INVALID_WORK_ITEM_SIZE;
  return clEnqueueTask(command_queue, kernel, num_events_in_wait_list,
                       event_wait_list, event);
}

cl_event clCreateUserEvent(cl_context context, cl_int *errcode_ret) {
  if (context != &g_cl_cxt) {
    errcode_is(CL_INVALID_CONTEXT);
    return NULL;
  }
  cl_event newev = alloc_cl_event(NULL);
  newev->status = CL_SUBMITTED;
  newev->t = CL_COMMAND_USER;
  errcode_is(CL_SUCCESS);
  clRetainEvent(newev);
  return newev;
}

cl_int clSetUserEventStatus(cl_event event, cl_int execution_status) {
  if (event->cmdq || event->t != CL_COMMAND_USER) return CL_INVALID_EVENT;
  if (execution_status != CL_COMPLETE) return CL_INVALID_VALUE;
  if (event->status == CL_COMPLETE) return CL_INVALID_OPERATION;
  event->status = CL_COMPLETE;
  return CL_SUCCESS;
}

cl_int clRetainEvent(cl_event event) {
  event->refcnt++;
  return CL_SUCCESS;
}

cl_int clReleaseEvent(cl_event event) {
  if (event->prev) clReleaseEvent(event->prev);
  if (event->next) clReleaseEvent(event->next);
  // do not manipulate cmdq->refcnt
  assert(event->refcnt > 0);
  event->refcnt--;
  if (!event->refcnt) {
    for (cl_uint i = 0; i < event->num_events_in_wait_list; ++i) {
      clReleaseEvent(event->event_wait_list[i]);
    }
    free(event->event_wait_list);
    switch (event->t) {
      case CL_COMMAND_READ_BUFFER:
        clReleaseMemObject(event->argWriteBuf.mem);
        break;
      case CL_COMMAND_WRITE_BUFFER:
        clReleaseMemObject(event->argReadBuf.mem);
        break;
      case CL_COMMAND_NDRANGE_KERNEL:
        clReleaseKernel(event->argKernel.k);
        break;
      default:
        break;
    }
    free(event);
  }
  return CL_SUCCESS;
}

cl_int clSetKernelArg(cl_kernel kernel, cl_uint arg_index, size_t arg_size,
                      const void *arg_value) {
  if (arg_index >= FPGARR_OPENCL_KERNEL_MAX_ARGS ||
      arg_index >= kernel->prog->spec.nargs)
    return CL_INVALID_ARG_INDEX;
  size_t expected_arg_size = 0;
  switch (kernel->prog->spec.args[arg_index]) {
    case KARG_CL_MEM:
      expected_arg_size = sizeof(cl_mem);
      break;
    case KARG_4B:
      expected_arg_size = sizeof(uint32_t);
      break;
    case KARG_8B:
      expected_arg_size = sizeof(uint64_t);
      break;
    default:
      return CL_INVALID_ARG_VALUE;
  }
  if (arg_size != expected_arg_size) {
    log_error("Invalid SetKernelArg size %ld, expected %ld", arg_size,
              expected_arg_size);
    return CL_INVALID_ARG_SIZE;
  }
  if (kernel->args_value[arg_index]) free(kernel->args_value[arg_index]);
  kernel->args_size[arg_index] = arg_size;
  kernel->args_value[arg_index] = malloc(arg_size);
  memcpy(kernel->args_value[arg_index], arg_value, arg_size);
  return CL_SUCCESS;
}

////////////// cl event utils ///////////////
// {{{
// only initialize the prev, next and refcnt
// only setup new cl_event refcnt with respect of the linked list
void enqueue_cl_event(cl_event event) {
  cl_event cmdheader = event->cmdq->cmdheader;
  event->prev = cmdheader->prev;
  event->next = cmdheader;
  cmdheader->prev = event;
  event->prev->next = event;
  clRetainEvent(event);
  clRetainEvent(event);
  if (event->cmdq->enableProfiling)
    event->profiling_info.ts_queued = getWallTimens();
}

cl_event alloc_cl_event(cl_command_queue cmdq) {
  cl_event newev = (cl_event)malloc(sizeof(struct _cl_event));
  newev->refcnt = 0;
  newev->prev = NULL;
  newev->next = NULL;
  newev->cmdq = cmdq;
  newev->profiling_info.ts_queued = 0;
  newev->profiling_info.ts_submit = 0;
  newev->profiling_info.ts_start = 0;
  newev->profiling_info.ts_end = 0;
  newev->num_events_in_wait_list = 0;
  newev->event_wait_list = NULL;
  return newev;
}

// do nothing if event is not in a double linked list
void linked_list_remove_cl_event(cl_event event) {
  if (event->prev && event->next) {
    event->prev->next = event->next;
    event->next->prev = event->prev;
    event->prev = NULL;
    event->next = NULL;
    clReleaseEvent(event);
    clReleaseEvent(event);
  } else {
    assert(!event->prev && !event->prev && "inconsistent double linked list");
  }
}

cl_int cl_command_exec(cl_event event) {
  if (event->cmdq->enableProfiling)
    event->profiling_info.ts_submit = getWallTimens();
  if (event->num_events_in_wait_list) {
    assert(clWaitForEvents(event->num_events_in_wait_list,
                           event->event_wait_list) == CL_SUCCESS);
  }
  if (event->cmdq->enableProfiling)
    event->profiling_info.ts_start = getWallTimens();
  cl_context cxt = event->cmdq->cxt;
  switch (event->t) {
    case CL_COMMAND_READ_BUFFER: {
      cl_mem m = event->argReadBuf.mem;
      assert(event->argReadBuf.offset + event->argReadBuf.size <= m->size &&
             "out of bound read");
      int rc =
          do_dma_read(cxt, event->argReadBuf.host_ptr, event->argReadBuf.size,
                      m->fpga_ddr_addr + event->argReadBuf.offset);
      if (rc != 0) return CL_INVALID_OPERATION;
      break;
    }
    case CL_COMMAND_WRITE_BUFFER: {
      cl_mem m = event->argWriteBuf.mem;
      assert(event->argWriteBuf.offset + event->argWriteBuf.size <= m->size &&
             "out of bound write");
      int rc = do_dma_write(cxt, event->argWriteBuf.host_ptr,
                            event->argWriteBuf.size,
                            m->fpga_ddr_addr + event->argWriteBuf.offset);
      if (rc != 0) return CL_INVALID_OPERATION;
      break;
    }
    case CL_COMMAND_NDRANGE_KERNEL: {
      cl_kernel k = event->argKernel.k;
      fake_program_spec_t *spec = &(k->prog->spec);
      // set args
      // this is a magic number known from generated verilog
      size_t csr_offset = 0x10;
      for (int i = 0; i < spec->nargs; ++i) {
        assert(k->args_value[i] && "Invalid args_value[i]");
        assert(k->args_size[i] && "Invalid args_size[i]");
        switch (spec->args[i]) {
          case KARG_CL_MEM: {
            cl_mem m = (cl_mem)(k->args_value[i]);
            poke_ocl64(cxt, csr_offset, m->fpga_ddr_addr);
            csr_offset += 8;
            break;
          }
          case KARG_4B:
            poke_ocl(cxt, csr_offset, *((uint32_t *)k->args_value[i]));
            csr_offset += 4;
            break;
          case KARG_8B:
            poke_ocl64(cxt, csr_offset, *((uint64_t *)k->args_value[i]));
            csr_offset += 8;
            break;
          default:
            return CL_INVALID_OPERATION;
        }
        // I do not know why but the vitis_hls seems to add a 4-byte reserved
        // padding.
        csr_offset += 0x4;
      }
      // start the kernel
      poke_ocl(cxt, 0x04, 1);  // Global Interrupt Enable
      poke_ocl(cxt, 0x08, 1);  // Enable ap_done interrupt
      poke_ocl(cxt, 0x00, 1);  // start
      // wait for kernel's completion
      wait_task_complete();
      // ap_continue, ack the design may continue running
      // I know this by referring to the Vitis Doc
      // https://docs.xilinx.com/r/en-US/ug1399-vitis-hls/Block-Level-Control-Protocols
      poke_ocl(cxt, 0x00, 0x10);
      // interrupt reg, clear the ap_done interrupt
      // I know this by looking at the generated control_axil verilog
      poke_ocl(cxt, 0x0c, 0x01);
      break;
    }
    default:
      return CL_INVALID_OPERATION;
  }
  if (event->cmdq->enableProfiling)
    event->profiling_info.ts_end = getWallTimens();
  event->status = CL_COMPLETE;
  return CL_SUCCESS;
}
// cl_event utils}}}
cl_int clWaitForEvents(cl_uint num_events, const cl_event *event_list) {
  if (num_events == 0 || event_list == NULL) return CL_INVALID_VALUE;
  for (cl_int i = 0; i < num_events; ++i) {
    cl_event e = event_list[i];
    // sanity check
    if (e->cmdq) {
      if (e->cmdq->cxt != &g_cl_cxt) return CL_INVALID_CONTEXT;
    } else {
      // UserEvent
      assert(e->status == CL_COMPLETE);
      assert(e->t == CL_COMMAND_USER);
    }
    if (e->status == CL_COMPLETE) continue;
    // respect wait list
    for (cl_uint j = 0; j < e->num_events_in_wait_list; ++j) {
      cl_int ret = clWaitForEvents(1, &(e->event_wait_list[j]));
      if (ret != CL_SUCCESS)
        return CL_EXEC_STATUS_ERROR_FOR_EVENTS_IN_WAIT_LIST;
    }
    if (cl_command_exec(e) != CL_SUCCESS)
      return CL_EXEC_STATUS_ERROR_FOR_EVENTS_IN_WAIT_LIST;
    linked_list_remove_cl_event(e);
  }
  return CL_SUCCESS;
}

cl_int clFlush(cl_command_queue command_queue) {
  return clFinish(command_queue);
}
cl_int clFinish(cl_command_queue command_queue) {
  while (command_queue->cmdheader->next != command_queue->cmdheader) {
    cl_event e = command_queue->cmdheader->next;
    assert(cl_command_exec(e) == CL_SUCCESS);
    linked_list_remove_cl_event(e);
  }
  return CL_SUCCESS;
}

cl_int clGetEventProfilingInfo(cl_event event, cl_profiling_info param_name,
                               size_t param_value_size, void *param_value,
                               size_t *param_value_size_ret) {
  if (event) {
    if (event->cmdq->enableProfiling) {
      if (param_value_size < sizeof(cl_ulong)) return CL_INVALID_VALUE;
      switch (param_name) {
        case CL_PROFILING_COMMAND_QUEUED:
          *((cl_ulong *)param_value) = event->profiling_info.ts_queued;
          break;
        case CL_PROFILING_COMMAND_SUBMIT:
          *((cl_ulong *)param_value) = event->profiling_info.ts_submit;
          break;
        case CL_PROFILING_COMMAND_START:
          *((cl_ulong *)param_value) = event->profiling_info.ts_start;
          break;
        case CL_PROFILING_COMMAND_END:
        case CL_PROFILING_COMMAND_COMPLETE:
          *((cl_ulong *)param_value) = event->profiling_info.ts_end;
          break;
        default:
          return CL_INVALID_VALUE;
      }
      if (param_value_size_ret) *param_value_size_ret = sizeof(cl_ulong);
      return CL_SUCCESS;
    } else
      return CL_PROFILING_INFO_NOT_AVAILABLE;
  } else
    return CL_INVALID_EVENT;
}

cl_int clGetContextInfo(cl_context context, cl_context_info param_name,
                        size_t param_value_size, void *param_value,
                        size_t *param_value_size_ret) {
  static cl_context_properties empty_cxt_props[] = {0};
  if (context != &g_cl_cxt) return CL_INVALID_CONTEXT;
  switch (param_name) {
    case CL_CONTEXT_REFERENCE_COUNT:
      CL_GET_INFO(cl_uint, context->refcnt);
      break;
    case CL_CONTEXT_NUM_DEVICES:
      CL_GET_INFO(cl_uint, context->num_devs);
      break;
    case CL_CONTEXT_DEVICES:
      CL_GET_INFO_MEMCPY(context->devs,
                         context->num_devs * sizeof(cl_device_id));
      break;
    case CL_CONTEXT_PROPERTIES:
      CL_GET_INFO_MEMCPY(&empty_cxt_props, sizeof(empty_cxt_props));
      break;
    default:
      return CL_INVALID_VALUE;
  }
  return CL_SUCCESS;
}

void print_fake_program_spec(fake_program_spec_t *p) {
  printf("nargs: %ld\n", p->nargs);
  for (size_t i = 0; i < p->nargs; ++i) {
    printf("fake_program_spec_t.args[%ld]=%d\n", i, p->args[i]);
  }
}

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
  int rc = 0;
  /* The statements within SCOPE ifdef below are needed for HW/SW
   * co-simulation with VCS */
#if defined(SCOPE)
  svScope scope;
  scope = svGetScopeFromName("tb");
  svSetScope(scope);
#endif

#if !defined(SV_TEST)
  /* initialize the fpga_plat library */
  rc = fpga_mgmt_init();
  fail_on(rc, err_out, "Unable to initialize the fpga_mgmt library");
#endif

#if defined(SV_TEST)
  // Set up DDR in simulation
  printf("Starting DDR init...\n");
  init_ddr();
  printf("Done DDR init...\n");
#endif

  // Init RR
  rc = init_rr(g_cl_cxt.slot_id);
  fail_on(rc, err_out, "init rr failed");
  do_pre_rr();
  fail_on(is_replay(), rr_out, "Skip application code, replaying");

  // Call the main function of HLS application
#ifdef SV_TEST
  rc = fpgarropencl_main(test_argc, test_argv);
#else
  rc = fpgarropencl_main(argc, argv);
#endif

rr_out:
  // Exit RR
  do_post_rr();
err_out:

#if !defined(SV_TEST)
  return rc;
#else
  if (rc != 0) {
    printf("TEST FAILED \n");
  } else {
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
