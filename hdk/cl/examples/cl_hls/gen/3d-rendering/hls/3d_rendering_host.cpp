/*===============================================================*/
/*                                                               */
/*                       3d_rendering.cpp                        */
/*                                                               */
/*      Main host function for the 3D Rendering application.     */
/*                                                               */
/*===============================================================*/

// standard C/C++ headers
#include <stdio.h>
#include <stdlib.h>
#include <getopt.h>
#include <time.h>
#include <sys/time.h>

// other headers
#include "typedefs.h"
#include "check_result.h"

// data
#include "input_data.h"

extern void rendering(bit32 input[NUM_3D_TRI*3], bit32 output[NUM_FB]);

int main(int argc, char ** argv) 
{
  printf("3D Rendering Application\n");

  // timers
  struct timeval start, end;

  // create space for input and output
  bit32* input  = new bit32[3 * NUM_3D_TRI];
  bit32* output = new bit32[NUM_FB];

  // pack input data for better performance
  for ( int i = 0; i < NUM_3D_TRI; i ++)
  {
    input[3*i](7,0)     = triangle_3ds[i].x0;
    input[3*i](15,8)    = triangle_3ds[i].y0;
    input[3*i](23,16)   = triangle_3ds[i].z0;
    input[3*i](31,24)   = triangle_3ds[i].x1;
    input[3*i+1](7,0)   = triangle_3ds[i].y1;
    input[3*i+1](15,8)  = triangle_3ds[i].z1;
    input[3*i+1](23,16) = triangle_3ds[i].x2;
    input[3*i+1](31,24) = triangle_3ds[i].y2;
    input[3*i+2](7,0)   = triangle_3ds[i].z2;
    input[3*i+2](31,8)  = 0;
  }


  // run and time sw function
  gettimeofday(&start, 0);
  rendering(input, output);
  gettimeofday(&end, 0);

  // check results
  printf("Checking results:\n");
  check_results(output);
 
  // print time
  long long elapsed = (end.tv_sec - start.tv_sec) * 1000000LL + end.tv_usec - start.tv_usec;   
  printf("elapsed time: %lld us\n", elapsed);

  delete []input;
  delete []output;

  return EXIT_SUCCESS;

}
