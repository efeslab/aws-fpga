/*===============================================================*/
/*                                                               */
/*                    optical_flow_host.cpp                      */
/*                                                               */
/*      Main host function for the Optical Flow application.     */
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

extern "C" {
#include "test_common.h"
}

#define MEM_1G (1LL*1024LL*1024LL*1024LL)

extern "C" int hls_main(int argc, char ** argv) 
{
  printf("Optical Flow Application\n");

  // parse command line arguments
  std::string dataPath = std::string(getenv("DATA_PATH"));
  std::string outFile = std::string(getenv("OUTFILE"));

  // create actual file names according to the datapath
  std::string frame_files[5];
  std::string reference_file;
  frame_files[0] = dataPath + "/frame1.ppm";
  frame_files[1] = dataPath + "/frame2.ppm";
  frame_files[2] = dataPath + "/frame3.ppm";
  frame_files[3] = dataPath + "/frame4.ppm";
  frame_files[4] = dataPath + "/frame5.ppm";
  reference_file = dataPath + "/ref.flo";

  // read in images and convert to grayscale
  printf("Reading input files ... \n");

  CByteImage imgs[5];
  for (int i = 0; i < 5; i++) 
  {
    CByteImage tmpImg;
    ReadImage(tmpImg, frame_files[i].c_str());
    imgs[i] = ConvertToGray(tmpImg);
  }

  // read in reference flow file
  printf("Reading reference output flow... \n");

  CFloatImage refFlow;
  ReadFlowFile(refFlow, reference_file.c_str());

  // timers
  struct timeval start, end;

  // input and output buffers
  static frames_t frames[MAX_HEIGHT][MAX_WIDTH];
  static velocity_t outputs[MAX_HEIGHT][MAX_WIDTH];

  // pack the values
  for (int i = 0; i < MAX_HEIGHT; i++) 
  {
    for (int j = 0; j < MAX_WIDTH; j++) 
    {
      frames[i][j](7 ,  0) = imgs[0].Pixel(j, i, 0);
      frames[i][j](15,  8) = imgs[1].Pixel(j, i, 0);
      frames[i][j](23, 16) = imgs[2].Pixel(j, i, 0);
      frames[i][j](31, 24) = imgs[3].Pixel(j, i, 0);
      frames[i][j](39, 32) = imgs[4].Pixel(j, i, 0);
      frames[i][j](63, 40) = 0;  
    }
  }
  printf("Start!\n");

  int rc = 0, slot_id = 0;
  const uint64_t accel_frame_addr = 0;
  const uint64_t accel_frame_size = MAX_HEIGHT*MAX_WIDTH*sizeof(frames_t);
  const uint64_t accel_output_addr = MEM_1G;
  const uint64_t accel_output_size = MAX_HEIGHT*MAX_WIDTH*sizeof(velocity_t);

  {
    do_dma_write((uint8_t*)frames, accel_frame_size, accel_frame_addr, 0, slot_id);
    fail_on(rc, out, "DMA write failed");

    //optical_flow(frames, outputs);
    hls_poke_ocl(0x04, 1);
    hls_poke_ocl(0x08, 1);
    hls_poke_ocl(0x10, accel_frame_addr & 0xffffffff);
    hls_poke_ocl(0x14, (accel_frame_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x1c, accel_output_addr & 0xffffffff);
    hls_poke_ocl(0x20, (accel_output_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x00, 1);

    hls_wait_task_complete(0x00);

    hls_poke_ocl(0x00, 1 << 4);
    hls_poke_ocl(0x0c, 1);

    do_dma_read((uint8_t*)outputs, accel_output_size, accel_output_addr, 0, slot_id);
    fail_on(rc, out, "DMA read failed");
  }

  // check results
  printf("Checking results:\n");

  check_results(outputs, refFlow, outFile);

out:
  return rc;
}
