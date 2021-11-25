/*
 * Amazon FPGA Hardware Development Kit
 *
 * Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Amazon Software License (the "License"). You may not use
 * this file except in compliance with the License. A copy of the License is
 * located at
 *
 *    http://aws.amazon.com/asl/
 *
 * or in the "license" file accompanying this file. This file is distributed on
 * an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, express or
 * implied. See the License for the specific language governing permissions and
 * limitations under the License.
 */

#pragma once

/**
 * Fills the buffer with bytes read from urandom.
 */
int fill_buffer_urandom(uint8_t *buf, size_t size);

/**
 * This function is like memcmp, but it returns the number of bytes that differ.
 *
 * @returns number of bytes which differ, i.e. zero if buffers are the same
 */
uint64_t buffer_compare(uint8_t *bufa, uint8_t *bufb,
    size_t buffer_size);

/**
 * Checks to make sure that the slot has a recognized AFI loaded.
 */
int check_slot_config(int slot_id);


#if defined(SV_TEST)
void setup_send_rdbuf_to_c(uint8_t *read_buffer, size_t buffer_size);
int send_rdbuf_to_c(char* rd_buf);
#endif

//Offset 0x00:
//             0 - Continuous mode - Keep looping through all the isntructions.
//             1 - Incrementing loop data (every time through loop increment the start data)
//             2 - PRBS mode (else incremeting).  Data will be generated with PRBS.  If not enabled, data will be incrementing per DW
//             3 - Read compare enable.  Do read compare.  Note if this is enabled the address/data in the read instructions must match the write instructinons
//             4 - Sync mode (read/write) -- This makes sure don't issue a read if write hasn't been issued (looking at wr_count/rd_count).  ***Generally should set this if Read Compare Enable.
//             5 - Iteration mode run for a certain number of iterations (see 0xc0)
//             6 - Loop higher address enable (enable shift/mask for higher addresses).  Each time through the loop will increment some upper address bits (see bits 13:8, 21:16)
//             7 - User ID mode - In this mode the USER bits come from the Instruction not from length (PCIe)
//
//             13:8 - Write Address loop shift (in higher address enable, how much to shift the loop count by).  Every time through the loop will increment a counter.  The counter will be logically OR'ed with the address.  This is how much to shift the counter by.
//             21:16 - Read Address loop shift.  Same thing for reads
//             24 - Incrementing ID mode (ID increments rather than first one available
//             25 - Constant data mode (all DW same)
typedef union {
    struct {
        uint8_t continuous : 1;       // 0
        uint8_t incLoopData : 1;      // 1
        uint8_t PRBS : 1;             // 2
        uint8_t readCompEn : 1;       // 3
        uint8_t syncEn : 1;           // 4
        uint8_t iterMode : 1;         // 5
        uint8_t loopHiAddrEn : 1;     // 6
        uint8_t userIDMode : 1;       // 7
        uint8_t wrAddrLoopShift : 6;  // 13:8
        uint8_t rdAddrLoopShift : 6;  // 21:16
        uint8_t rsvd : 2;             // 23:22
        uint8_t incIDMode : 1;        // 24
        uint8_t constData : 1;        // 25
        uint8_t unused : 6;           // 31:26
    };
    uint32_t val;
} pcim_tst_cfg_t;
