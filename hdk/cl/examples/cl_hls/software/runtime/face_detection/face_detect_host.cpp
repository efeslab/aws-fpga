/*===============================================================*/
/*                                                               */
/*                       face_detect.cpp                         */
/*                                                               */
/*     Main host function for the Face Detection application.    */
/*                                                               */
/*===============================================================*/

// standard C/C++ headers
#include <cstdio>
#include <cstdlib>
#include <getopt.h>
#include <string>
#include <time.h>
#include <sys/time.h>

// other headers
#include "utils.h"
#include "typedefs.h"
#include "check_result.h"

// data
#include "image0_320_240.h"

extern "C" {
#include "test_common.h"
}

#define MEM_1G (1LL*1024LL*1024LL*1024LL)
#define NUM_LOOP 1000

extern "C" int hls_main(int argc, char ** argv) 
{
  printf("Face Detection Application\n");

  std::string outFile("ofile.pgm");

  // for this benchmark, input data is included in array Data
  // these are outputs
  int result_x[RESULT_SIZE];
  int result_y[RESULT_SIZE];
  int result_w[RESULT_SIZE];
  int result_h[RESULT_SIZE];
  int res_size = 0;

  int rc = 0;
  int slot_id = 0;
  int int_status_reg = 0;

  const uint64_t accel_indata_addr = 0;
  const uint64_t accel_result_x_addr = MEM_1G;
  const uint64_t accel_result_y_addr = MEM_1G * 2;
  const uint64_t accel_result_w_addr = MEM_1G * 3;
  const uint64_t accel_result_h_addr = MEM_1G * 4;

  for (int i=0; i < NUM_LOOP; ++i) {
    rc = do_dma_write((uint8_t*)Data, IMAGE_SIZE, accel_indata_addr, 0, slot_id);
    fail_on(rc, out, "DMA write failed");

    // res_size = face_detect((uint8_t*)Data, result_x, result_y, result_w, result_h);
    hls_poke_ocl(0x04, 1); // Global Interrupt Enable
    hls_poke_ocl(0x08, 1); // Enable ap_done Interrupt
    hls_poke_ocl(0x18, accel_indata_addr & 0xffffffff);
    hls_poke_ocl(0x1c, (accel_indata_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x24, accel_result_x_addr & 0xffffffff);
    hls_poke_ocl(0x28, (accel_result_x_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x30, accel_result_y_addr & 0xffffffff);
    hls_poke_ocl(0x34, (accel_result_y_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x3c, accel_result_w_addr & 0xffffffff);
    hls_poke_ocl(0x40, (accel_result_w_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x48, accel_result_h_addr & 0xffffffff);
    hls_poke_ocl(0x4c, (accel_result_h_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x00, 1);

    hls_wait_task_complete(0x00);
    hls_peek_ocl(0x10, (uint32_t*)&res_size);

#ifdef DBG_CSR_LOG
    hls_peek_ocl(0x0c, &int_status_reg);
    printf("interrupt status: %d\n", int_status_reg);
#endif

    hls_poke_ocl(0x00, 1 << 4); // make it continue
    hls_poke_ocl(0x0c, 1);
#ifdef DBG_CSR_LOG
    hls_peek_ocl(0x0c, &int_status_reg);
    printf("interrupt status: %d\n", int_status_reg);
#endif

    rc = do_dma_read((uint8_t*)result_x, res_size*sizeof(int), accel_result_x_addr, 0, slot_id);
    fail_on(rc, out, "DMA read failed");
    rc = do_dma_read((uint8_t*)result_y, res_size*sizeof(int), accel_result_y_addr, 0, slot_id);
    fail_on(rc, out, "DMA read failed");
    rc = do_dma_read((uint8_t*)result_w, res_size*sizeof(int), accel_result_w_addr, 0, slot_id);
    fail_on(rc, out, "DMA read failed");
    rc = do_dma_read((uint8_t*)result_h, res_size*sizeof(int), accel_result_h_addr, 0, slot_id);
    fail_on(rc, out, "DMA read failed");
  }

  // check results
  printf("Checking results:\n");
  check_results(res_size, result_x, result_y, result_w, result_h, Data, outFile);
    
out:
  return rc;
}
