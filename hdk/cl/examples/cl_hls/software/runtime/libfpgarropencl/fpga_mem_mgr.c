#include "fpga_mem_mgr.h"

// very simple linear allocation, no dealloc
#define MEM_16G (1ULL << 34)
#define XCL_MEM_DDR_BANK0_BASEADDR (0)
#define XCL_MEM_DDR_BANK1_BASEADDR (XCL_MEM_DDR_BANK0_BASEADDR + MEM_16G)
#define XCL_MEM_DDR_BANK2_BASEADDR (XCL_MEM_DDR_BANK1_BASEADDR + MEM_16G)
#define XCL_MEM_DDR_BANK3_BASEADDR (XCL_MEM_DDR_BANK2_BASEADDR + MEM_16G)
const uint64_t XCL_MEM_DDR_BASEADDR[NUMBANK] = {
  [0] = XCL_MEM_DDR_BANK0_BASEADDR,
  [1] = XCL_MEM_DDR_BANK1_BASEADDR,
  [2] = XCL_MEM_DDR_BANK2_BASEADDR,
  [3] = XCL_MEM_DDR_BANK3_BASEADDR
};
uint64_t allocated_sizeB[NUMBANK] = {0};

int fpga_alloc_bank(uint8_t bank_id, size_t sizeB, uint64_t *addr) {
  if (bank_id >= 0 && bank_id < NUMBANK) {
    // the allocated_sizeB is the base address of the next allocation
    uint64_t aligned_addr = MEM_ALIGN_UP(allocated_sizeB[bank_id]);
    if (aligned_addr + sizeB < MEM_16G) {
      allocated_sizeB[bank_id] = aligned_addr + sizeB;
      *addr = XCL_MEM_DDR_BASEADDR[bank_id] + aligned_addr;
      return 0;
    }
  }
  return -1;
}

// always allocate at the least used bank
int fpga_alloc(size_t sizeB, uint64_t *addr) {
  uint8_t min_bank_id = 0;
  uint64_t min_allocated_sizeB = UINT64_MAX;
  for (uint8_t i = 0; i < NUMBANK; ++i) {
    if (allocated_sizeB[i] < min_allocated_sizeB) {
      min_allocated_sizeB = allocated_sizeB[i];
      min_bank_id = i;
    }
  }
  return fpga_alloc_bank(min_bank_id, sizeB, addr);
}
