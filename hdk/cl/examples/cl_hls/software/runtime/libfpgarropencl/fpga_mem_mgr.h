#ifndef LIBFPGARROPENCL_FPGA_MEM_MGR_H
#define LIBFPGARROPENCL_FPGA_MEM_MGR_H
#include <stddef.h>
#include <stdint.h>
#define MEM_ALIGNMENT (512)
#define MEM_ALIGN_UP(x) ((x+(MEM_ALIGNMENT-1)) & ~(MEM_ALIGNMENT-1))
#define MEM_ALIGN_DOWN(x) (x & ~(MEM_ALIGNMENT-1))
#define NUMBANK 4
// return 0 success
// bank_id: {0,1,2..(NUMBANK-1)}
// allocate memory on specific FPGA DDR
// ret: address stored to addr
extern int fpga_alloc_bank(uint8_t bank_id, size_t sizeB, uint64_t *addr);
// return 0 success
// automatic distribute among different banks
// ret: address stored to addr
extern int fpga_alloc(size_t sizeB, uint64_t *addr);
#endif // LIBFPGARROPENCL_FPGA_MEM_MGR_H
