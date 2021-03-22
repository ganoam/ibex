// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

`include "prim_assert.sv"

/**
 * Top level module of the ibex RISC-V core complex
 */
module ibex_cc #(
    parameter bit                 PMPEnable                            = 1'b0,
    parameter int unsigned        PMPGranularity                       = 0,
    parameter int unsigned        PMPNumRegions                        = 4,
    parameter int unsigned        MHPMCounterNum                       = 0,
    parameter int unsigned        MHPMCounterWidth                     = 40,
    parameter bit                 RV32E                                = 1'b0,
    parameter ibex_pkg::rv32m_e   RV32M                                = ibex_pkg::RV32MFast,
    parameter ibex_pkg::rv32b_e   RV32B                                = ibex_pkg::RV32BNone,
    parameter ibex_pkg::regfile_e RegFile                              = ibex_pkg::RegFileFF,
    parameter bit                 BranchTargetALU                      = 1'b0,
    parameter bit                 WritebackStage                       = 1'b0,
    parameter bit                 ICache                               = 1'b0,
    parameter bit                 ICacheECC                            = 1'b0,
    parameter bit                 BranchPredictor                      = 1'b0,
    parameter bit                 DbgTriggerEn                         = 1'b0,
    parameter int unsigned        DbgHwBreakNum                        = 1,
    parameter bit                 SecureIbex                           = 1'b0,
    parameter int unsigned        DmHaltAddr                           = 32'h1A110800,
    parameter int unsigned        DmExceptionAddr                      = 32'h1A110808,
    parameter bit                 XInterface                           = 1'b1,
    parameter bit                 XInterfaceTernaryOps                 = 1'b1
) (
    // Clock and Reset
    input  logic                         clk_i,
    input  logic                         rst_ni,

    input  logic                         test_en_i,     // enable all clock gates for testing
    input  prim_ram_1p_pkg::ram_1p_cfg_t ram_cfg_i,

    input  logic [31:0]                  hart_id_i,
    input  logic [31:0]                  boot_addr_i,

    // Instruction memory interface
    output logic                         instr_req_o,
    input  logic                         instr_gnt_i,
    input  logic                         instr_rvalid_i,
    output logic [31:0]                  instr_addr_o,
    input  logic [31:0]                  instr_rdata_i,
    input  logic                         instr_err_i,

    // Data memory interface
    output logic                         data_req_o,
    input  logic                         data_gnt_i,
    input  logic                         data_rvalid_i,
    output logic                         data_we_o,
    output logic [3:0]                   data_be_o,
    output logic [31:0]                  data_addr_o,
    output logic [31:0]                  data_wdata_o,
    input  logic [31:0]                  data_rdata_i,
    input  logic                         data_err_i,

    // Interrupt inputs
    input  logic                         irq_software_i,
    input  logic                         irq_timer_i,
    input  logic                         irq_external_i,
    input  logic [14:0]                  irq_fast_i,
    input  logic                         irq_nm_i,       // non-maskeable interrupt

    // Debug Interface
    input  logic                         debug_req_i,
    output ibex_pkg::crash_dump_t        crash_dump_o,

    // RISC-V Extension Interface
    input  acc_pkg::acc_c_rsp_t          acc_c_rsp_i,
    output acc_pkg::acc_c_req_t          acc_c_req_o,

    output acc_pkg::acc_cmem_rsp_t       acc_cmem_rsp_o,
    input  acc_pkg::acc_cmem_req_t       acc_cmem_req_i,

    // RISC-V Formal Interface
    // Does not comply with the coding standards of _i/_o suffixes, but follows
    // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
    output logic                         rvfi_valid,
    output logic [63:0]                  rvfi_order,
    output logic [31:0]                  rvfi_insn,
    output logic                         rvfi_trap,
    output logic                         rvfi_halt,
    output logic                         rvfi_intr,
    output logic [ 1:0]                  rvfi_mode,
    output logic [ 1:0]                  rvfi_ixl,
    output logic [ 4:0]                  rvfi_rs1_addr,
    output logic [ 4:0]                  rvfi_rs2_addr,
    output logic [ 4:0]                  rvfi_rs3_addr,
    output logic [31:0]                  rvfi_rs1_rdata,
    output logic [31:0]                  rvfi_rs2_rdata,
    output logic [31:0]                  rvfi_rs3_rdata,
    output logic [ 4:0]                  rvfi_rd_addr,
    output logic [31:0]                  rvfi_rd_wdata,
    output logic [31:0]                  rvfi_pc_rdata,
    output logic [31:0]                  rvfi_pc_wdata,
    output logic [31:0]                  rvfi_mem_addr,
    output logic [ 3:0]                  rvfi_mem_rmask,
    output logic [ 3:0]                  rvfi_mem_wmask,
    output logic [31:0]                  rvfi_mem_rdata,
    output logic [31:0]                  rvfi_mem_wdata,
`endif

    // CPU Control Signals
    input  logic                         fetch_enable_i,
    output logic                         alert_minor_o,
    output logic                         alert_major_o,
    output logic                         core_sleep_o
);

  acc_pkg::acc_x_req_t acc_x_req;
  acc_pkg::acc_x_rsp_t acc_x_rsp;

  acc_pkg::acc_prd_req_t [acc_pkg::NumRspTot-1:0] acc_prd_req;
  acc_pkg::acc_prd_rsp_t [acc_pkg::NumRspTot-1:0] acc_prd_rsp;

  acc_pkg::acc_c_req_t acc_c_req_adapter;
  acc_pkg::acc_c_rsp_t acc_c_rsp_adapter;

  acc_pkg::acc_c_req_t [acc_pkg::NumRsp[0]-1:0] acc_c_req;
  acc_pkg::acc_c_rsp_t [acc_pkg::NumRsp[0]-1:0] acc_c_rsp;

  acc_pkg::acc_xmem_req_t acc_xmem_req;
  acc_pkg::acc_xmem_rsp_t acc_xmem_rsp;

  acc_pkg::acc_cmem_req_t acc_cmem_req_adapter;
  acc_pkg::acc_cmem_rsp_t acc_cmem_rsp_adapter;

  acc_pkg::acc_cmem_req_t [acc_pkg::NumRsp[0]-1:0] acc_cmem_req;
  acc_pkg::acc_cmem_rsp_t [acc_pkg::NumRsp[0]-1:0] acc_cmem_rsp;

  logic        acc_x_q_valid;
  logic        acc_x_q_ready;
  logic [31:0] acc_x_q_instr_data;
  logic [31:0] acc_x_q_rs1;
  logic [31:0] acc_x_q_rs2;
  logic [31:0] acc_x_q_rs3;
  logic [ 2:0] acc_x_q_rs_valid;
  logic        acc_x_q_rd_clean;
  logic        acc_x_k_writeback;
  logic        acc_x_k_accept;

  logic        acc_x_p_valid;
  logic        acc_x_p_ready;
  logic [4:0]  acc_x_p_rd;
  logic [31:0] acc_x_p_data;
  logic        acc_x_p_error;

  ibex_core #(
    .PMPEnable            ( PMPEnable            ),
    .PMPGranularity       ( PMPGranularity       ),
    .PMPNumRegions        ( PMPNumRegions        ),
    .MHPMCounterNum       ( MHPMCounterNum       ),
    .MHPMCounterWidth     ( MHPMCounterWidth     ),
    .RV32E                ( RV32E                ),
    .RV32M                ( RV32M                ),
    .RV32B                ( RV32B                ),
    .RegFile              ( RegFile              ),
    .BranchTargetALU      ( BranchTargetALU      ),
    .ICache               ( ICache               ),
    .ICacheECC            ( ICacheECC            ),
    .BranchPredictor      ( BranchPredictor      ),
    .DbgTriggerEn         ( DbgTriggerEn         ),
    .DbgHwBreakNum        ( DbgHwBreakNum        ),
    .WritebackStage       ( WritebackStage       ),
    .SecureIbex           ( SecureIbex           ),
    .DmHaltAddr           ( DmHaltAddr           ),
    .DmExceptionAddr      ( DmExceptionAddr      ),
    .XInterface           ( XInterface           ),
    .XInterfaceTernaryOps ( XInterfaceTernaryOps )
  ) u_ibex_core (
    .clk_i          ( clk_i          ),
    .rst_ni         ( rst_ni         ),

    .test_en_i      ( test_en_i      ),
    .ram_cfg_i      ( ram_cfg_i      ),

    .hart_id_i      ( hart_id_i      ),
    .boot_addr_i    ( boot_addr_i    ),

    .instr_req_o    ( instr_req_o    ),
    .instr_gnt_i    ( instr_gnt_i    ),
    .instr_rvalid_i ( instr_rvalid_i ),
    .instr_addr_o   ( instr_addr_o   ),
    .instr_rdata_i  ( instr_rdata_i  ),
    .instr_err_i    ( instr_err_i    ),

    .data_req_o     ( data_req_o     ),
    .data_gnt_i     ( data_gnt_i     ),
    .data_rvalid_i  ( data_rvalid_i  ),
    .data_we_o      ( data_we_o      ),
    .data_be_o      ( data_be_o      ),
    .data_addr_o    ( data_addr_o    ),
    .data_wdata_o   ( data_wdata_o   ),
    .data_rdata_i   ( data_rdata_i   ),
    .data_err_i     ( data_err_i     ),

    .irq_software_i ( irq_software_i ),
    .irq_timer_i    ( irq_timer_i    ),
    .irq_external_i ( irq_external_i ),
    .irq_fast_i     ( irq_fast_i     ),
    .irq_nm_i       ( irq_nm_i       ),

    .debug_req_i    ( debug_req_i    ),
    .crash_dump_o   ( crash_dump_o   ),

    .rvfi_valid     ( rvfi_valid     ),
    .rvfi_order     ( rvfi_order     ),
    .rvfi_insn      ( rvfi_insn      ),
    .rvfi_trap      ( rvfi_trap      ),
    .rvfi_halt      ( rvfi_halt      ),
    .rvfi_intr      ( rvfi_intr      ),
    .rvfi_mode      ( rvfi_mode      ),
    .rvfi_ixl       ( rvfi_ixl       ),
    .rvfi_rs1_addr  ( rvfi_rs1_addr  ),
    .rvfi_rs2_addr  ( rvfi_rs2_addr  ),
    .rvfi_rs3_addr  ( rvfi_rs3_addr  ),
    .rvfi_rs1_rdata ( rvfi_rs1_rdata ),
    .rvfi_rs2_rdata ( rvfi_rs2_rdata ),
    .rvfi_rs3_rdata ( rvfi_rs3_rdata ),
    .rvfi_rd_addr   ( rvfi_rd_addr   ),
    .rvfi_rd_wdata  ( rvfi_rd_wdata  ),
    .rvfi_pc_rdata  ( rvfi_pc_rdata  ),
    .rvfi_pc_wdata  ( rvfi_pc_wdata  ),
    .rvfi_mem_addr  ( rvfi_mem_addr  ),
    .rvfi_mem_rmask ( rvfi_mem_rmask ),
    .rvfi_mem_wmask ( rvfi_mem_wmask ),
    .rvfi_mem_rdata ( rvfi_mem_rdata ),
    .rvfi_mem_wdata ( rvfi_mem_wdata ),

    // RISC-V Extension Interface
    .acc_x_q_valid_o      ( acc_x_q_valid      ),
    .acc_x_q_ready_i      ( acc_x_q_ready      ),
    .acc_x_q_instr_data_o ( acc_x_q_instr_data ),
    .acc_x_q_rs1_o        ( acc_x_q_rs1        ),
    .acc_x_q_rs2_o        ( acc_x_q_rs2        ),
    .acc_x_q_rs3_o        ( acc_x_q_rs3        ),
    .acc_x_q_rs_valid_o   ( acc_x_q_rs_valid   ),
    .acc_x_q_rd_clean_o   ( acc_x_q_rd_clean   ),
    .acc_x_k_writeback_i  ( acc_x_k_writeback  ),
    .acc_x_k_accept_i     ( acc_x_k_accept     ),

    .acc_x_p_valid_i ( acc_x_p_valid ),
    .acc_x_p_ready_o ( acc_x_p_ready ),
    .acc_x_p_rd_i    ( acc_x_p_rd    ),
    .acc_x_p_data_i  ( acc_x_p_data  ),
    .acc_x_p_error_i ( acc_x_p_error ),


    .fetch_enable_i ( fetch_enable_i ),
    .alert_minor_o  ( alert_minor_o  ),
    .alert_major_o  ( alert_major_o  ),
    .core_sleep_o   ( core_sleep_o   )
  );

  assign acc_x_req.q_valid      = acc_x_q_valid;
  assign acc_x_req.q.instr_data = acc_x_q_instr_data;
  assign acc_x_req.q.rs[0]      = acc_x_q_rs1;
  assign acc_x_req.q.rs[1]      = acc_x_q_rs2;
  assign acc_x_req.q.rs[2]      = acc_x_q_rs3;
  assign acc_x_req.q.rs_valid   = acc_x_q_rs_valid;
  assign acc_x_req.q.rd_clean   = acc_x_q_rd_clean;

  assign acc_x_q_ready     = acc_x_rsp.q_ready;
  assign acc_x_k_writeback = acc_x_rsp.k.writeback[0];
  assign acc_x_k_accept    = acc_x_rsp.k.accept;


  assign acc_x_p_valid = acc_x_rsp.p_valid;
  assign acc_x_p_rd    = acc_x_rsp.p.rd;
  assign acc_x_p_data  = acc_x_rsp.p.data[0];
  assign acc_x_p_error = acc_x_rsp.p.error;

  assign acc_x_req.p_ready = acc_x_p_ready;

  logic        unused_acc_x_p_dualwb;

  assign unused_acc_x_p_dualwb = acc_x_rsp.p.dualwb;

  acc_adapter acc_adapter_i (
    .clk_i          ( clk_i                ),
    .rst_ni         ( rst_ni               ),
    .hart_id_i      ( hart_id_i            ),
    .acc_x_req_i    ( acc_x_req            ),
    .acc_x_rsp_o    ( acc_x_rsp            ),
    .acc_c_req_o    ( acc_c_req_adapter    ),
    .acc_c_rsp_i    ( acc_c_rsp_adapter    ),
    .acc_xmem_req_o ( acc_xmem_req         ),
    .acc_xmem_rsp_i ( acc_xmem_rsp         ),
    .acc_cmem_req_i ( acc_cmem_req_adapter ),
    .acc_cmem_rsp_o ( acc_cmem_rsp_adapter ),
    .acc_prd_req_o  ( acc_prd_req          ),
    .acc_prd_rsp_i  ( acc_prd_rsp          )
  );

  acc_predecoder #(
    .NumInstr     ( acc_rvb_pkg::NumInstr ),
    .OffloadInstr ( acc_rvb_pkg::Instr    )
  ) acc_rvb_predecoder_i (
    .prd_req_i ( acc_prd_req ),
    .prd_rsp_o ( acc_prd_rsp )
  );

  acc_interconnect #(
    .HierLevel   ( 0                       ),
    .NumReq      ( 1                       ),
    .NumRsp      ( acc_pkg::NumRsp[0]      ),
    .RegisterReq ( acc_pkg::RegisterReq[0] ),
    .RegisterRsp ( acc_pkg::RegisterRsp[0] )
  ) acc_interconnect_i (
    .clk_i                   ( clk_i                ),
    .rst_ni                  ( rst_ni               ),
    .acc_c_slv_req_i         ( acc_c_req_adapter    ),
    .acc_c_slv_rsp_o         ( acc_c_rsp_adapter    ),
    .acc_cmem_mst_req_o      ( acc_cmem_req_adapter ),
    .acc_cmem_mst_rsp_i      ( acc_cmem_rsp_adapter ),
    .acc_c_mst_next_req_o    ( acc_c_req_o          ),
    .acc_c_mst_next_rsp_i    ( acc_c_rsp_i          ),
    .acc_cmem_slv_next_req_i ( acc_cmem_req_i       ),
    .acc_cmem_slv_next_rsp_o ( acc_cmem_rsp_o       ),
    .acc_c_mst_req_o         ( acc_c_req            ),
    .acc_c_mst_rsp_i         ( acc_c_rsp            ),
    .acc_cmem_slv_req_i      ( acc_cmem_req         ),
    .acc_cmem_slv_rsp_o      ( acc_cmem_rsp         )
  );

  rvb_full #(
    .XLEN ( 32 )
  ) acc_rvb_i (
    .clock       ( clk_i                     ),
    .reset       ( !rst_ni                   ),
    .din_valid   ( acc_c_req[0].q_valid      ),
    .din_ready   ( acc_c_rsp[0].q_ready      ),
    .din_decoded ( /* unused */              ),
    .din_rs1     ( acc_c_req[0].q.rs[0]      ),
    .din_rs2     ( acc_c_req[0].q.rs[1]      ),
    .din_rs3     ( acc_c_req[0].q.rs[2]      ),
    .din_insn    ( acc_c_req[0].q.instr_data ),
    .dout_valid  ( acc_c_rsp[0].p_valid      ),
    .dout_ready  ( acc_c_req[0].p_ready      ),
    .dout_rd     ( acc_c_rsp[0].p.rd         ),
    .dout_data   ( acc_c_rsp[0].p.data[0]    )
  );

endmodule
