/*===============================================================*/
/*                                                               */
/*                        spam_filter.cpp                        */
/*                                                               */
/*      Main host function for the Spam Filter application.      */
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

extern "C" int hls_main(int argc, char *argv[]) 
{
  setbuf(stdout, NULL);

  printf("Spam Filter Application\n");

  // parse command line arguments
  std::string path_to_data("");
  //parse_sdsoc_command_line_args(argc, argv, path_to_data);
  path_to_data = std::string(getenv("PATH_TO_DATA"));

  // allocate space
  // for software verification
  DataType*    data_points  = new DataType[DATA_SET_SIZE];
  LabelType*   labels       = new LabelType  [NUM_SAMPLES];
  FeatureType* param_vector = new FeatureType[NUM_FEATURES];

  // read in dataset
  std::string str_points_filepath = path_to_data + "/shuffledfeats.dat";
  std::string str_labels_filepath = path_to_data + "/shuffledlabels.dat";

  FILE* data_file;
  FILE* label_file;

  data_file = fopen(str_points_filepath.c_str(), "r");
  if (!data_file)
  {
    printf("Failed to open data file %s!\n", str_points_filepath.c_str());
    return EXIT_FAILURE;
  }
  for (int i = 0; i < DATA_SET_SIZE; i ++ )
  {
    float tmp;
    fscanf(data_file, "%f", &tmp);
    data_points[i] = tmp;
  }
  fclose(data_file);

  label_file = fopen(str_labels_filepath.c_str(), "r");
  if (!label_file)
  {
    printf("Failed to open label file %s!\n", str_labels_filepath.c_str());
    return EXIT_FAILURE;
  }
  for (int i = 0; i < NUM_SAMPLES; i ++ )
  {
    int tmp;
    fscanf(label_file, "%d", &tmp);
    labels[i] = tmp;
  }
  fclose(label_file);

  // reset parameter vector
  for (size_t i = 0; i < NUM_FEATURES; i++)
    param_vector[i] = 0;

  // allocate space for accelerator
  VectorDataType* data_points_for_accel = (VectorDataType*)aligned_alloc(4096, sizeof(VectorDataType) * NUM_TRAINING * NUM_FEATURES / D_VECTOR_SIZE);
  VectorLabelType* labels_for_accel = (VectorLabelType*)aligned_alloc(4096, sizeof(VectorLabelType) * NUM_TRAINING / L_VECTOR_SIZE);
  VectorFeatureType* param_for_accel = (VectorFeatureType*)aligned_alloc(4096, sizeof(VectorFeatureType) * NUM_FEATURES / F_VECTOR_SIZE);
 
  // reorganize data for the accelerator
  // data points
  for (int i = 0; i < NUM_TRAINING * NUM_FEATURES / D_VECTOR_SIZE; i ++ )
    for (int j = 0; j < D_VECTOR_SIZE; j ++ )
      data_points_for_accel[i].range((j+1)*DTYPE_TWIDTH-1, j*DTYPE_TWIDTH) = data_points[i*D_VECTOR_SIZE+j].range(DTYPE_TWIDTH-1, 0);
  
  // labels
  for (int i = 0; i < NUM_TRAINING / L_VECTOR_SIZE; i ++ )
    for (int j = 0; j < L_VECTOR_SIZE; j ++ )
      labels_for_accel[i].range((j+1)*LTYPE_WIDTH-1, j*LTYPE_WIDTH) = labels[i*L_VECTOR_SIZE+j].range(LTYPE_WIDTH-1, 0);
  
  // parameter vector
  for (int i = 0; i < NUM_FEATURES / F_VECTOR_SIZE; i ++ )
    for (int j = 0; j < F_VECTOR_SIZE; j ++ )
      param_for_accel[i].range((j+1)*FTYPE_TWIDTH-1, j*FTYPE_TWIDTH) = param_vector[i*F_VECTOR_SIZE+j].range(FTYPE_TWIDTH-1, 0);

  int rc = 0;
  int slot_id = 0;
  const uint64_t data_points_for_accel_addr = 0;
  const uint64_t labels_for_accel_addr = MEM_1G;
  const uint64_t param_for_accel_addr = MEM_1G * 2;
  const uint64_t data_points_for_accel_size = sizeof(VectorDataType) * NUM_TRAINING * NUM_FEATURES / D_VECTOR_SIZE;
  const uint64_t labels_for_accel_size = sizeof(VectorLabelType) * NUM_TRAINING / L_VECTOR_SIZE;
  const uint64_t param_for_accel_size = sizeof(VectorFeatureType) * NUM_FEATURES / F_VECTOR_SIZE;

  printf("data_points_for_accel_size: %d\n", data_points_for_accel_size);
  printf("labels_for_accel_size: %d\n", labels_for_accel_size);
  printf("param_for_accel_size: %d\n", param_for_accel_size);

  rc = do_dma_write((uint8_t*)data_points_for_accel, data_points_for_accel_size, data_points_for_accel_addr, 0, slot_id);
  fail_on(rc, out, "DMA write failed");
  printf("data points done\n");
  rc = do_dma_write((uint8_t*)labels_for_accel, labels_for_accel_size, labels_for_accel_addr, 0, slot_id);
  fail_on(rc, out, "DMA write failed");
  printf("labels done\n");
  rc = do_dma_write((uint8_t*)param_for_accel, param_for_accel_size, param_for_accel_addr, 0, slot_id);
  fail_on(rc, out, "DMA write failed");
  printf("param done\n");
  
  // run the accelerator
  for (int epoch = 0; epoch < NUM_EPOCHS; epoch ++ )
  {
    printf("epoch %d...\n", epoch);
    //SgdLR(data_points_for_accel, labels_for_accel, param_for_accel, (epoch == 0), (epoch == 4));
    hls_poke_ocl(0x04, 1);
    hls_poke_ocl(0x08, 1);
    hls_poke_ocl(0x10, data_points_for_accel_addr & 0xffffffff);
    hls_poke_ocl(0x14, (data_points_for_accel_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x1c, labels_for_accel_addr & 0xffffffff);
    hls_poke_ocl(0x20, (labels_for_accel_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x28, param_for_accel_addr & 0xffffffff);
    hls_poke_ocl(0x2c, (param_for_accel_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x34, (epoch == 0));
    hls_poke_ocl(0x3c, (epoch == NUM_EPOCHS - 1));
    hls_poke_ocl(0x00, 1);

    hls_wait_task_complete(0x00);

    hls_poke_ocl(0x00, 1 << 4);
    hls_poke_ocl(0x0c, 1);
  }

  rc = do_dma_read((uint8_t*)param_for_accel, param_for_accel_size, param_for_accel_addr, 0, slot_id);
  fail_on(rc, out, "DMA read failed");
  
  // reorganize the parameter vector
  for (int i = 0; i < NUM_FEATURES / F_VECTOR_SIZE; i ++ )
    for (int j = 0; j < F_VECTOR_SIZE; j ++ )
      param_vector[i*F_VECTOR_SIZE+j].range(FTYPE_TWIDTH-1, 0) = param_for_accel[i].range((j+1)*FTYPE_TWIDTH-1, j*FTYPE_TWIDTH);

  // check results
  printf("Checking results:\n");
  check_results( param_vector, data_points, labels );
    
out:
  free(data_points_for_accel);
  free(labels_for_accel);
  free(param_for_accel);

  delete []data_points;
  delete []labels;
  delete []param_vector;

  return EXIT_SUCCESS;
}
