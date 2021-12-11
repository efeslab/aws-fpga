/*===============================================================*/
/*                                                               */
/*                       face_detect.h                           */
/*                                                               */
/*     Hardware function for the Face Detection application.     */
/*                                                               */
/*===============================================================*/


#include "typedefs.h"

extern "C" int face_detect( unsigned char inData[IMAGE_HEIGHT * IMAGE_WIDTH], 
                  int result_x[RESULT_SIZE], 
                  int result_y[RESULT_SIZE], 
                  int result_w[RESULT_SIZE], 
                  int result_h[RESULT_SIZE]);

