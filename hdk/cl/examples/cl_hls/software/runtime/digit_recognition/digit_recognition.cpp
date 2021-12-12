/*===============================================================*/
/*                                                               */
/*                    digit_recognition.cpp                      */
/*                                                               */
/*   Main host function for the Digit Recognition application.   */
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
#include "training_data.h"
#include "testing_data.h"

extern "C" {
#include "test_common.h"
}

#define MEM_1G (1LL*1024LL*1024LL*1024LL)
#define NUM_LOOP 1000

extern "C" int hls_main(int argc, char ** argv) 
{
  printf("Digit Recognition Application\n");

  // for this benchmark, data is already included in arrays:
  //   training_data: contains 18000 training samples, with 1800 samples for each digit class
  //   testing_data:  contains 2000 test samples
  //   expected:      contains labels for the test samples

  // timers
  struct timeval start, end;
  int rc = 0;
  int slot_id = 0;
  uint32_t int_status_reg;

  // sdsoc version host code
  // allocate space for hardware function
  WholeDigitType* training_in0 = (WholeDigitType*)malloc(sizeof(WholeDigitType) * NUM_TRAINING / 2);
  WholeDigitType* training_in1 = (WholeDigitType*)malloc(sizeof(WholeDigitType) * NUM_TRAINING / 2);
  WholeDigitType* test_in      = (WholeDigitType*)malloc(sizeof(WholeDigitType) * NUM_TEST);
  
  // pack the data into a wide datatype
  for (int i = 0; i < NUM_TRAINING / 2; i ++ )
  {
    training_in0[i].range(63 , 0  ) = training_data[i*DIGIT_WIDTH+0];
    training_in0[i].range(127, 64 ) = training_data[i*DIGIT_WIDTH+1];
    training_in0[i].range(191, 128) = training_data[i*DIGIT_WIDTH+2];
    training_in0[i].range(255, 192) = training_data[i*DIGIT_WIDTH+3];
  }
  for (int i = 0; i < NUM_TRAINING / 2; i ++ )
  {
    training_in1[i].range(63 , 0  ) = training_data[(NUM_TRAINING / 2 + i)*DIGIT_WIDTH+0];
    training_in1[i].range(127, 64 ) = training_data[(NUM_TRAINING / 2 + i)*DIGIT_WIDTH+1];
    training_in1[i].range(191, 128) = training_data[(NUM_TRAINING / 2 + i)*DIGIT_WIDTH+2];
    training_in1[i].range(255, 192) = training_data[(NUM_TRAINING / 2 + i)*DIGIT_WIDTH+3];
  }
  
  for (int i = 0; i < NUM_TEST; i ++ )
  {
    test_in[i].range(63 , 0  ) = testing_data[i*DIGIT_WIDTH+0];
    test_in[i].range(127, 64 ) = testing_data[i*DIGIT_WIDTH+1];
    test_in[i].range(191, 128) = testing_data[i*DIGIT_WIDTH+2];
    test_in[i].range(255, 192) = testing_data[i*DIGIT_WIDTH+3];
  }

  // create space for result
  LabelType* result = (LabelType*)malloc(sizeof(LabelType) * NUM_TEST);

  rr_user_timer_begin();

  const uint64_t accel_traning_in0_addr = 0;
  const uint64_t accel_traning_in1_addr = MEM_1G;
  const uint64_t accel_test_in_addr = MEM_1G * 2;
  const uint64_t accel_result_addr = MEM_1G * 3;
  const uint64_t training_in0_size = sizeof(WholeDigitType) * NUM_TRAINING / 2;
  const uint64_t training_in1_size = sizeof(WholeDigitType) * NUM_TRAINING / 2;
  const uint64_t test_in_size = sizeof(WholeDigitType) * NUM_TEST;
  const uint64_t result_size = sizeof(LabelType) * NUM_TEST;

  for (int i=0; i < NUM_LOOP; ++i) {
    rc = do_dma_write((uint8_t*)training_in0, training_in0_size, accel_traning_in0_addr, 0, slot_id);
    fail_on(rc, out, "DMA write failed");
    rc = do_dma_write((uint8_t*)training_in1, training_in1_size, accel_traning_in1_addr, 0, slot_id);
    fail_on(rc, out, "DMA write failed");
    rc = do_dma_write((uint8_t*)test_in, test_in_size, accel_test_in_addr, 0, slot_id);
    fail_on(rc, out, "DMA write failed");

    // run the hardware function
    // first call: transfer data
    //DigitRec(training_in0, test_in, result, 0);
    hls_poke_ocl(0x04, 1); // Enable Global Interrupt
    hls_poke_ocl(0x08, 1); // Enable ap_done Interrupt
    hls_poke_ocl(0x10, accel_traning_in0_addr & 0xffffffff);
    hls_poke_ocl(0x14, (accel_traning_in0_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x1c, accel_test_in_addr & 0xffffffff);
    hls_poke_ocl(0x20, (accel_test_in_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x28, accel_result_addr & 0xffffffff);
    hls_poke_ocl(0x2c, (accel_result_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x34, 0);
    hls_poke_ocl(0x00, 1);

#ifdef DBG_CSR_LOG
    printf("wait for completion\n");
#endif
    hls_wait_task_complete(0x00);

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

    // second call: execute
    //DigitRec(training_in1, test_in, result, 1);
    hls_poke_ocl(0x04, 1); // Enable Global Interrupt
    hls_poke_ocl(0x08, 1); // Enable ap_done Interrupt
    hls_poke_ocl(0x10, accel_traning_in1_addr & 0xffffffff);
    hls_poke_ocl(0x14, (accel_traning_in1_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x1c, accel_test_in_addr & 0xffffffff);
    hls_poke_ocl(0x20, (accel_test_in_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x28, accel_result_addr & 0xffffffff);
    hls_poke_ocl(0x2c, (accel_result_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x34, 1);
    hls_poke_ocl(0x00, 1);

#ifdef DBG_CSR_LOG
    printf("wait for completion\n");
#endif
    hls_wait_task_complete(0x00);

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

    do_dma_read((uint8_t*)result, result_size, accel_result_addr, 0, slot_id);
    fail_on(rc, out, "DMA read failed");

  }
  rr_user_timer_end();

  // check results
  printf("Checking results:\n");
  check_results( result, expected, NUM_TEST );

out:
    
  free(training_in0);
  free(training_in1);
  free(test_in);
  free(result);

  return EXIT_SUCCESS;

}
