#ifndef CL_FPGARR_TRACE_CONTENT_H
#define CL_FPGARR_TRACE_CONTENT_H
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>

#include "bitStreamIO.hpp"
// some basic config parameters
#define PACKET_ALIGNMENT 8
// x is bits
constexpr size_t GET_ALIGNED_BITS(size_t x) {
  return (x + PACKET_ALIGNMENT - 1) & (~(PACKET_ALIGNMENT - 1));
}
// x is bits
constexpr size_t GET_ALIGNED_BYTES(size_t x) {
  return (x + PACKET_ALIGNMENT - 1) / PACKET_ALIGNMENT;
}

/*
 * The `__attribute__((packed))` cannot guarantee bit-level alignment in struct,
 * so the following definition just illustrates the different fields of each
 * type of channel packet but does not serve as a binary representation.
 */
typedef struct {
  uint8_t awsize : 3;
  uint8_t awlen : 8;
  uint64_t awaddr: 64;
  uint16_t awid : 16;
} F1_AXI_AW_t;
typedef struct {
  uint8_t wlast : 1;
  uint64_t wstrb : 64;
  uint8_t wdata[64];
  uint16_t wid : 16;
} F1_AXI_W_t;
typedef struct {
  uint8_t arsize : 3;
  uint8_t arlen : 8;
  uint64_t araddr;
  uint16_t arid : 16;
} F1_AXI_AR_t;
typedef struct {
  uint8_t bresp : 2;
  uint16_t bid : 16;
} F1_AXI_B_t;
typedef struct {
  uint8_t rlast : 1;
  uint8_t rresp : 2;
  uint8_t rdata[64];
  uint16_t rid : 16;
} F1_AXI_R_t;
typedef struct {
  uint32_t awaddr;
} F1_AXIL_AW_t;
typedef struct {
  uint8_t wstrb : 4;
  uint32_t wdata : 32;
} F1_AXIL_W_t;
typedef struct {
  uint32_t araddr;
} F1_AXIL_AR_t;
typedef struct {
  uint8_t bresp : 2;
} F1_AXIL_B_t;
typedef struct {
  uint8_t rresp : 2;
  uint32_t rdata : 32;
} F1_AXIL_R_t;

struct F1PktType {
  typedef enum {
    AXI_AW = 0, AXI_W, AXI_AR, AXI_B, AXI_R,  // F1_AXI
    AXIL_AW, AXIL_W, AXIL_AR, AXIL_B, AXIL_R, // F1_AXI
    NUM_TID,
    INVALID
  } type;
  static constexpr size_t tid_bits[NUM_TID] = {
    [AXI_AW] = 91,
    [AXI_W] = 593,
    [AXI_AR] = 91,
    [AXI_B] = 18,
    [AXI_R] = 531,
    [AXIL_AW] = 32,
    [AXIL_W] = 36,
    [AXIL_AR] = 32,
    [AXIL_B] = 2,
    [AXIL_R] = 34,
  };
  static constexpr const char *axi_intfs[] = {"pcis", "pcim"};
  static constexpr const char *axil_intfs[] = {"ocl", "bar1", "sda"};
  static type getType(const char *intf_name, size_t intf_len,
                      const char *ch_name, size_t ch_len);
};
struct F1ChannelPkt_t {
  F1PktType::type tid;
  F1ChannelPkt_t(F1PktType::type _tid, const void *raw_data, size_t sizeB)
      : tid(_tid) {
    decode_raw_data(raw_data, sizeB);
  }
  union {
    F1_AXI_AW_t as_AXI_AW;
    F1_AXI_W_t as_AXI_W;
    F1_AXI_AR_t as_AXI_AR;
    F1_AXI_B_t as_AXI_B;
    F1_AXI_R_t as_AXI_R;
    F1_AXIL_AW_t as_AXIL_AW;
    F1_AXIL_W_t as_AXIL_W;
    F1_AXIL_AR_t as_AXIL_AR;
    F1_AXIL_B_t as_AXIL_B;
    F1_AXIL_R_t as_AXIL_R;
  };

  void decode_raw_data(const void *raw_data, size_t sizeB);
  // update the struct with another packet
  void refill(F1PktType::type _tid, const void *raw_data, size_t sizeB);
  void markInvalid() { tid = F1PktType::INVALID; }
  void printPkt(FILE *fp) const;
  static void printBinary(FILE *fp, const void *data, size_t sizeB);
};
#endif  // CL_FPGARR_TRACE_CONTENT_H
