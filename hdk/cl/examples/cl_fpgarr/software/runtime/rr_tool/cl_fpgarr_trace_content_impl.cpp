#include "cl_fpgarr_trace_content.hpp"
#include "cl_fpgarr_utils.hpp"
#include <cassert>

F1PktType::type F1PktType::getType(const char *intf_name, size_t intf_len,
                                   const char *ch_name, size_t ch_len) {
  bool isAXI =
      findStringInArray(intf_name, intf_len, axi_intfs, ARRAY_LEN(axi_intfs));
  bool isAXIL =
      findStringInArray(intf_name, intf_len, axil_intfs, ARRAY_LEN(axil_intfs));
  assert(isAXI ^ isAXIL && "Invalid intf_name");
  if (strncmp(ch_name, "AW", ch_len) == 0)
    return isAXI ? AXI_AW : AXIL_AW;
  else if (strncmp(ch_name, "W", ch_len) == 0)
    return isAXI ? AXI_W : AXIL_W;
  else if (strncmp(ch_name, "AR", ch_len) == 0)
    return isAXI ? AXI_AR : AXIL_AR;
  else if (strncmp(ch_name, "B", ch_len) == 0)
    return isAXI ? AXI_B : AXIL_B;
  else if (strncmp(ch_name, "R", ch_len) == 0)
    return isAXI ? AXI_R : AXIL_R;
  else {
    assert(0 && "Invalid ch_name");
    return INVALID;
  }
}

void F1ChannelPkt_t::decode_raw_data(const void *_raw_data, size_t sizeB) {
  assert(GET_ALIGNED_BYTES(F1PktType::tid_bits[tid]) <= sizeB);
  ibitstream ibits(_raw_data, sizeB);
  switch (tid) {
    case F1PktType::AXI_AW:
      as_AXI_AW.awsize = ibits.getNbits<uint8_t>(3);
      as_AXI_AW.awlen = ibits.getNbits<uint8_t>(8);
      as_AXI_AW.awaddr = ibits.getNbits<uint64_t>(64);
      as_AXI_AW.awid = ibits.getNbits<uint16_t>(16);
      break;
    case F1PktType::AXI_W:
      as_AXI_W.wlast = ibits.getNbits<uint8_t>(1);
      as_AXI_W.wstrb = ibits.getNbits<uint64_t>(64);
      ibits.getNbits_ptr(as_AXI_W.wdata, 512);
      as_AXI_W.wid = ibits.getNbits<uint16_t>(16);
      break;
    case F1PktType::AXI_AR:
      as_AXI_AR.arsize = ibits.getNbits<uint8_t>(3);
      as_AXI_AR.arlen = ibits.getNbits<uint8_t>(8);
      as_AXI_AR.araddr = ibits.getNbits<uint64_t>(64);
      as_AXI_AR.arid = ibits.getNbits<uint16_t>(16);
      break;
    case F1PktType::AXI_B:
      as_AXI_B.bresp = ibits.getNbits<uint8_t>(2);
      as_AXI_B.bid = ibits.getNbits<uint16_t>(16);
      break;
    case F1PktType::AXI_R:
      as_AXI_R.rlast = ibits.getNbits<uint8_t>(1);
      as_AXI_R.rresp = ibits.getNbits<uint8_t>(2);
      ibits.getNbits_ptr(as_AXI_R.rdata, 512);
      as_AXI_R.rid = ibits.getNbits<uint16_t>(16);
      break;
    case F1PktType::AXIL_AW:
      as_AXIL_AW.awaddr = ibits.getNbits<uint32_t>(32);
      break;
    case F1PktType::AXIL_W:
      as_AXIL_W.wstrb = ibits.getNbits<uint8_t>(4);
      as_AXIL_W.wdata = ibits.getNbits<uint32_t>(32);
      break;
    case F1PktType::AXIL_AR:
      as_AXIL_AR.araddr = ibits.getNbits<uint32_t>(32);
      break;
    case F1PktType::AXIL_B:
      as_AXIL_B.bresp = ibits.getNbits<uint8_t>(2);
      break;
    case F1PktType::AXIL_R:
      as_AXIL_R.rresp = ibits.getNbits<uint8_t>(2);
      as_AXIL_R.rdata = ibits.getNbits<uint32_t>(32);
      break;
    default:
      assert(0 && "Invalid PktType");
  }
}

void F1ChannelPkt_t::refill(F1PktType::type _tid, const void *raw_data,
                            size_t sizeB) {
  tid = _tid;
  decode_raw_data(raw_data, sizeB);
}

void F1ChannelPkt_t::printPkt(FILE *fp) const {
  switch (tid) {
    case F1PktType::AXI_AW:
      fprintf(fp, "awid %d, awsize %d, awlen %d, awaddr %#lx", as_AXI_AW.awid,
              as_AXI_AW.awsize, as_AXI_AW.awlen, as_AXI_AW.awaddr);
      break;
    case F1PktType::AXI_W:
      fprintf(fp, "wid %d, wstrb %#lx, wlast %d, wdata ", as_AXI_W.wid,
              as_AXI_W.wstrb, as_AXI_W.wlast);
      printBinary(fp, as_AXI_W.wdata, 64);
      break;
    case F1PktType::AXI_AR:
      fprintf(fp, "arid %d, arsize %d, arlen %d, araddr %#lx", as_AXI_AR.arid,
              as_AXI_AR.arsize, as_AXI_AR.arlen, as_AXI_AR.araddr);
      break;
    case F1PktType::AXI_B:
      fprintf(fp, "bid %d, bresp %d", as_AXI_B.bid, as_AXI_B.bresp);
      break;
    case F1PktType::AXI_R:
      fprintf(fp, "rid %d, rresp %d, rlast %d, rdata ", as_AXI_R.rid,
              as_AXI_R.rresp, as_AXI_R.rlast);
      printBinary(fp, as_AXI_R.rdata, 64);
      break;
    case F1PktType::AXIL_AW:
      fprintf(fp, "awaddr %#x", as_AXIL_AW.awaddr);
      break;
    case F1PktType::AXIL_W:
      fprintf(fp, "wstrb %#x, wdata %#x", as_AXIL_W.wstrb, as_AXIL_W.wdata);
      break;
    case F1PktType::AXIL_AR:
      fprintf(fp, "araddr %#x", as_AXIL_AR.araddr);
      break;
    case F1PktType::AXIL_B:
      fprintf(fp, "bresp %d", as_AXIL_B.bresp);
      break;
    case F1PktType::AXIL_R:
      fprintf(fp, "rresp %d, rdata %#x", as_AXIL_R.rresp, as_AXIL_R.rdata);
      break;
    default:
      assert(0 && "Invalid PktType");
      fprintf(fp, "Invalid PktType");
  }
}

void F1ChannelPkt_t::printBinary(FILE *fp, const void *data, size_t sizeB) {
  const uint8_t *p = static_cast<const uint8_t*>(data);
  fprintf(fp, "0x");
  for (uint8_t i = sizeB; i > 0; --i) {
    fprintf(fp, "%02x", p[i - 1]);
  }
}
