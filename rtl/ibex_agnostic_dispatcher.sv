// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Agnostic instruction dispatcher
 */

module ibex_agnostic_dispatcher #(
    parameter bit XInterfaceTernaryOps    = 1'b0,
    parameter bit XInterfaceDualWriteback = 1'b0
) (
    // Clock and Reset
    input  logic                      clk_i,
    input  logic                      rst_ni,

    input  logic                      test_en_i,     // enable all clock gates for testing

    input  logic                      illegal_insn_dec_i,
    input  logic [31:0]               instr_data_i,
    input  logic                      instr_first_cycle_i,

    output logic                      is_offload_o,
    input  logic [31:0]               rf_rdata_a_fwd_i,
    input  logic [31:0]               rf_rdata_b_fwd_i,
    input  logic [31:0]               imd_val_i, // intermediate storage of rs1.

    output logic                      offload_rf_we_o,


    // Accelerator X interface request
    output logic                      acc_x_q_valid_o,
    output logic [31:0]               acc_x_q_rs1_o,
    output logic [31:0]               acc_x_q_rs2_o,
    output logic [31:0]               acc_x_q_rs3_o,
    output logic [ 2:0]               acc_x_q_rs_valid_o,
    output logic [ 1:0]               acc_x_q_rd_clean_o,
    input  logic                      acc_x_q_ready_i,
    input  logic [ 1:0]               acc_x_k_writeback_i,
    input  logic                      acc_x_k_accept_i,

    // Accelerator X interface response
    input  logic                      acc_x_p_valid_i,
    input  logic [1:0][31:0]          acc_x_p_data_i,
    input  logic                      acc_x_p_dualwb_i,
    input  logic                      acc_x_p_error_i,
    output logic                      acc_x_p_ready_o
  );

  // X Interface
  localparam int NumRegs = RV32E ? 16 : 32;

  logic [4:0] instr_rs1;
  logic [4:0] instr_rs2;
  logic [4:0] instr_rs3;
  logic [4:0] instr_rd;
  logic [4:0] instr_rd_plusone;

  logic [2:0] acc_x_q_rs_scb_valid;
  logic [1:0] acc_x_q_rd_scb_valid;

  assign instr_rs1 = instr[19:15];
  assign instr_rs2 = instr[24:20];
  assign instr_rs3 = instr[31:27];
  assign instr_rd  = instr[11:7];
  assign instr_rd_plusone = instr[11:7] | 5'b00001;


  logic [2:0] acc_x_rs_scb_valid;

  // dual writeback only for even rd address
  assign acc_x_q_rd_scb_valid[1] =
    (instr_rd[0] == 1'b0) ? (XInterfaceDualWriteback && scoreboard_q[instr_rd_plusone]) : 1'b0;


  always_comb begin

    if (illegal_insn_dec_i) begin
      acc_x_q_valid_o = 1'b1
    end

  end


  endmodule

