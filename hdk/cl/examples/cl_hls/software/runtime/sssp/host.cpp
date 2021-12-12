/**********
Copyright (c) 2017, Xilinx, Inc.
All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

1. Redistributions of source code must retain the above copyright notice,
this list of conditions and the following disclaimer.

2. Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation
and/or other materials provided with the distribution.

3. Neither the name of the copyright holder nor the names of its contributors
may be used to endorse or promote products derived from this software
without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
**********/
//#include "xcl2.hpp"
#include "graph.hpp"
#include <vector>
#include <stdexcept>
#include <string>
#include <limits>

using std::vector;
using std::string;
using graph::Graph;
using graph::Edge;

static constexpr double kInfinity = std::numeric_limits<double>::max();
static const std::string error_message =
    "Error: Result mismatch:\n"
    "i = %d CPU result = %d Device result = %d\n";

extern "C" {
#include "test_common.h"
}

#define MEM_1G (1LL*1024LL*1024LL*1024LL)

template <typename T>
struct aligned_allocator
{
  using value_type = T;
  T* allocate(std::size_t num)
  {
    void* ptr = nullptr;
    if (posix_memalign(&ptr,4096,num*sizeof(T)))
      throw std::bad_alloc();
    return reinterpret_cast<T*>(ptr);
  }
  void deallocate(T* p, std::size_t num)
  {
    free(p);
  }
};

extern "C" int hls_main(int argc, char **argv) {

    string inputFile = string(getenv("DATA_FILE"));
    int source = 0;
    if(argc == 3) {
        string inputFile = argv[1];
        string sourceStr = argv[2];
        int source = std::stoi(sourceStr); 
    }

	printf("inputFile: %s\n", inputFile.c_str());

    Graph graph = Graph(inputFile);

    // compute the size of array in bytes
    // size_t size_in_bytes = DATA_SIZE * sizeof(int);

    // Creates a vector of DATA_SIZE elements with an initial value of 10 and 32
    vector<double, aligned_allocator<double>> distsRead(graph.num_vertices, kInfinity);
    vector<double, aligned_allocator<double>> distsWrite(graph.num_vertices, kInfinity);
    distsRead[source] = 0.0;
    distsWrite[source] = 0.0;
    vector<size_t, aligned_allocator<size_t>> sources(graph.getNumEdges());
    vector<size_t, aligned_allocator<size_t>> destinations(graph.getNumEdges());
    vector<double, aligned_allocator<double>> costs(graph.getNumEdges());

    vector<Edge> allEdges = graph.getAllEdges();
    for(size_t i=0; i<allEdges.size(); i++) {
        sources[i] = allEdges[i].src;
        destinations[i] = allEdges[i].dest;
        costs[i] = allEdges[i].cost;
    }

    const uint64_t distsRead_addr = 0;
    const uint64_t distsWrite_addr = MEM_1G;
    const uint64_t sources_addr = MEM_1G * 2;
    const uint64_t destinations_addr = MEM_1G * 3;
    const uint64_t costs_addr = MEM_1G * 4;

    //bellman_ford(distsRead.data(), distsWrite.data(), sources.data(), destinations.data(), costs.data(),
    //        graph.num_vertices, graph.getNumEdges());
    int rc = 0, slot_id = 0;
    rc = do_dma_write((uint8_t*)distsRead.data(), graph.num_vertices * sizeof(double), distsRead_addr, 0, slot_id);
	fail_on(rc, out, "DMA write failed");
    rc = do_dma_write((uint8_t*)distsWrite.data(), graph.num_vertices * sizeof(double), distsWrite_addr, 0, slot_id);
	fail_on(rc, out, "DMA write failed");
    rc = do_dma_write((uint8_t*)sources.data(), graph.getNumEdges() * sizeof(size_t), sources_addr, 0, slot_id);
	fail_on(rc, out, "DMA write failed");
    rc = do_dma_write((uint8_t*)destinations.data(), graph.getNumEdges() * sizeof(size_t), destinations_addr, 0, slot_id);
	fail_on(rc, out, "DMA write failed");
    rc = do_dma_write((uint8_t*)costs.data(), graph.getNumEdges() * sizeof(double), costs_addr, 0, slot_id);
	fail_on(rc, out, "DMA write failed");

    hls_poke_ocl(0x04, 1);
    hls_poke_ocl(0x08, 1);
    hls_poke_ocl(0x10, distsRead_addr & 0xffffffff);
    hls_poke_ocl(0x14, (distsRead_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x1c, distsWrite_addr & 0xffffffff);
    hls_poke_ocl(0x20, (distsWrite_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x28, sources_addr & 0xffffffff);
    hls_poke_ocl(0x2c, (sources_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x34, destinations_addr & 0xffffffff);
    hls_poke_ocl(0x38, (destinations_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x40, costs_addr & 0xffffffff);
    hls_poke_ocl(0x44, (costs_addr >> 32) & 0xffffffff);
    hls_poke_ocl(0x4c, graph.num_vertices & 0xffffffff);
    hls_poke_ocl(0x50, (graph.num_vertices >> 32) & 0xffffffff);
    hls_poke_ocl(0x58, graph.getNumEdges() & 0xffffffff);
    hls_poke_ocl(0x5c, (graph.getNumEdges() >> 32) & 0xffffffff);
    hls_poke_ocl(0x00, 1);

    hls_wait_task_complete(0x00);

    hls_poke_ocl(0x00, 1 << 4);
    hls_poke_ocl(0x0c, 1);

    rc = do_dma_read((uint8_t*)distsRead.data(), graph.num_vertices * sizeof(double), distsRead_addr, 0, slot_id);
	fail_on(rc, out, "DMA read failed");

    for (int i = 0; i < graph.num_vertices; i++) {
        printf("%d: %lf\n", i, distsRead[i]);
    }

out:
    return rc;
}
