// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_tb_top;

  import uvm_pkg::*;
  import core_ibex_test_pkg::*;

  wire clk;
  wire rst_n;
  logic fetch_enable;

  clk_rst_if     ibex_clk_if(.clk(clk), .rst_n(rst_n));
  irq_if         irq_vif(.clk(clk));
  ibex_mem_intf  data_mem_vif(.clk(clk));
  ibex_mem_intf  instr_mem_vif(.clk(clk));


  // DUT probe interface
  core_ibex_dut_probe_if dut_if(.clk(clk));

  // Instruction monitor interface
  core_ibex_instr_monitor_if instr_monitor_if(.clk(clk));

  // RVFI interface
  core_ibex_rvfi_if rvfi_if(.clk(clk));

  // CSR access interface
  core_ibex_csr_if csr_if(.clk(clk));

  // VCS does not support overriding enum and string parameters via command line. Instead, a
  // `define is used that can be set from the command line. If no value has been specified, this
  // gives a default. Other simulators don't take the detour via `define and can override the
  // corresponding parameters directly.
  `ifndef IBEX_CFG_RV32M
    `define IBEX_CFG_RV32M ibex_pkg::RV32MFast
  `endif

  `ifndef IBEX_CFG_RV32B
    `define IBEX_CFG_RV32B ibex_pkg::RV32BNone
  `endif

  `ifndef IBEX_CFG_RegFile
    `define IBEX_CFG_RegFile ibex_pkg::RegFileFF
  `endif

  parameter bit          PMPEnable      = 1'b0;
  parameter int unsigned PMPGranularity = 0;
  parameter int unsigned PMPNumRegions  = 4;
  parameter bit RV32E                   = 1'b0;
  parameter ibex_pkg::rv32m_e RV32M     = `IBEX_CFG_RV32M;
  parameter ibex_pkg::rv32b_e RV32B     = `IBEX_CFG_RV32B;
  parameter ibex_pkg::regfile_e RegFile = `IBEX_CFG_RegFile;
  parameter bit BranchTargetALU         = 1'b0;
  parameter bit WritebackStage          = 1'b0;
  parameter bit ICache                  = 1'b0;
  parameter bit ICacheECC               = 1'b0;
  parameter bit BranchPredictor         = 1'b0;
  parameter bit XInterface              = 1'b0;
  parameter bit XInterfaceTernaryOps    = 1'b0;

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

  logic [31:0] hart_id;
  assign hart_id = 32'h0;

  ibex_top_tracing #(
    .DmHaltAddr           ( 32'h`BOOT_ADDR + 'h0 ),
    .DmExceptionAddr      ( 32'h`BOOT_ADDR + 'h4 ),
    .PMPEnable            ( PMPEnable            ),
    .PMPGranularity       ( PMPGranularity       ),
    .PMPNumRegions        ( PMPNumRegions        ),
    .RV32E                ( RV32E                ),
    .RV32M                ( RV32M                ),
    .RV32B                ( RV32B                ),
    .RegFile              ( RegFile              ),
    .BranchTargetALU      ( BranchTargetALU      ),
    .WritebackStage       ( WritebackStage       ),
    .ICache               ( ICache               ),
    .ICacheECC            ( ICacheECC            ),
    .BranchPredictor      ( BranchPredictor      ),
    .XInterface           ( XInterface           ),
    .XInterfaceTernaryOps ( XInterfaceTernaryOps )
  ) dut (
    .clk_i                (clk                  ),
    .rst_ni               (rst_n                ),

    .test_en_i            (1'b0                 ),
    .scan_rst_ni          (1'b1                 ),
    .ram_cfg_i            ('b0                  ),

    .hart_id_i            (hart_id              ),
    .boot_addr_i          (32'h`BOOT_ADDR       ), // align with spike boot address

    .instr_req_o          (instr_mem_vif.request),
    .instr_gnt_i          (instr_mem_vif.grant  ),
    .instr_rvalid_i       (instr_mem_vif.rvalid ),
    .instr_addr_o         (instr_mem_vif.addr   ),
    .instr_rdata_i        (instr_mem_vif.rdata  ),
    .instr_err_i          (instr_mem_vif.error  ),

    .data_req_o           (data_mem_vif.request ),
    .data_gnt_i           (data_mem_vif.grant   ),
    .data_rvalid_i        (data_mem_vif.rvalid  ),
    .data_addr_o          (data_mem_vif.addr    ),
    .data_we_o            (data_mem_vif.we      ),
    .data_be_o            (data_mem_vif.be      ),
    .data_rdata_i         (data_mem_vif.rdata   ),
    .data_wdata_o         (data_mem_vif.wdata   ),
    .data_err_i           (data_mem_vif.error   ),

    .irq_software_i       (irq_vif.irq_software ),
    .irq_timer_i          (irq_vif.irq_timer    ),
    .irq_external_i       (irq_vif.irq_external ),
    .irq_fast_i           (irq_vif.irq_fast     ),
    .irq_nm_i             (irq_vif.irq_nm       ),

    .acc_x_q_valid_o      (acc_x_q_valid        ),
    .acc_x_q_ready_i      (acc_x_q_ready        ),
    .acc_x_q_instr_data_o (acc_x_q_instr_data   ),
    .acc_x_q_rs1_o        (acc_x_q_rs1          ),
    .acc_x_q_rs2_o        (acc_x_q_rs2          ),
    .acc_x_q_rs3_o        (acc_x_q_rs3          ),
    .acc_x_q_rs_valid_o   (acc_x_q_rs_valid     ),
    .acc_x_q_rd_clean_o   (acc_x_q_rd_clean     ),
    .acc_x_k_writeback_i  (acc_x_k_writeback    ),
    .acc_x_k_accept_i     (acc_x_k_accept       ),

    .acc_x_p_valid_i      (acc_x_p_valid        ),
    .acc_x_p_ready_o      (acc_x_p_ready        ),
    .acc_x_p_rd_i         (acc_x_p_rd           ),
    .acc_x_p_data_i       (acc_x_p_data         ),
    .acc_x_p_error_i      (acc_x_p_error        ),

    .debug_req_i          (dut_if.debug_req     ),
    .crash_dump_o         (                     ),

    .fetch_enable_i       (dut_if.fetch_enable  ),
    .alert_minor_o        (dut_if.alert_minor   ),
    .alert_major_o        (dut_if.alert_major   ),
    .core_sleep_o         (dut_if.core_sleep    )
  );

  // X Interface connections and modules
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

  logic  unused_acc_x_p_dualwb;
  assign unused_acc_x_p_dualwb = acc_x_rsp.p.dualwb;

  acc_adapter acc_adapter_i (
    .clk_i          ( clk                  ),
    .rst_ni         ( rst_n                ),
    .hart_id_i      ( hart_id              ),
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
    .clk_i                   ( clk                  ),
    .rst_ni                  ( rst_n                ),
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

  assign acc_c_rsp[0].p.hart_id = hart_id;

  rvb_full #(
    .XLEN ( 32 )
  ) acc_rvb_i (
    .clock       ( clk                       ),
    .reset       ( !rst_n                    ),
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

  // Data load/store vif connection
  assign data_mem_vif.reset                   = ~rst_n;
  // Instruction fetch vif connnection
  assign instr_mem_vif.reset                  = ~rst_n;
  assign instr_mem_vif.we                     = 0;
  assign instr_mem_vif.be                     = 0;
  assign instr_mem_vif.wdata                  = 0;
  // RVFI interface connections
  assign rvfi_if.valid                        = dut.rvfi_valid;
  assign rvfi_if.order                        = dut.rvfi_order;
  assign rvfi_if.insn                         = dut.rvfi_insn;
  assign rvfi_if.trap                         = dut.rvfi_trap;
  assign rvfi_if.intr                         = dut.rvfi_intr;
  assign rvfi_if.mode                         = dut.rvfi_mode;
  assign rvfi_if.ixl                          = dut.rvfi_ixl;
  assign rvfi_if.rs1_addr                     = dut.rvfi_rs1_addr;
  assign rvfi_if.rs2_addr                     = dut.rvfi_rs2_addr;
  assign rvfi_if.rs1_rdata                    = dut.rvfi_rs1_rdata;
  assign rvfi_if.rs2_rdata                    = dut.rvfi_rs2_rdata;
  assign rvfi_if.rd_addr                      = dut.rvfi_rd_addr;
  assign rvfi_if.rd_wdata                     = dut.rvfi_rd_wdata;
  assign rvfi_if.pc_rdata                     = dut.rvfi_pc_rdata;
  assign rvfi_if_pc_wdata                     = dut.rvfi_pc_wdata;
  assign rvfi_if.mem_addr                     = dut.rvfi_mem_addr;
  assign rvfi_if.mem_rmask                    = dut.rvfi_mem_rmask;
  assign rvfi_if.mem_rdata                    = dut.rvfi_mem_rdata;
  assign rvfi_if.mem_wdata                    = dut.rvfi_mem_wdata;
  // Irq interface connections
  assign irq_vif.reset                        = ~rst_n;
  // Dut_if interface connections
  assign dut_if.ecall                         = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.ecall_insn;
  assign dut_if.wfi                           = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.wfi_insn;
  assign dut_if.ebreak                        = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.ebrk_insn;
  assign dut_if.illegal_instr                 = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.illegal_insn_d;
  assign dut_if.dret                          = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.dret_insn;
  assign dut_if.mret                          = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.mret_insn;
  assign dut_if.reset                         = ~rst_n;
  assign dut_if.priv_mode                     = dut.u_ibex_top.u_ibex_core.priv_mode_id;
  // Instruction monitor connections
  assign instr_monitor_if.valid_id            = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_valid_i;
  assign instr_monitor_if.err_id              = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.instr_fetch_err;
  assign instr_monitor_if.is_compressed_id    = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_is_compressed_i;
  assign instr_monitor_if.instr_compressed_id = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_rdata_c_i;
  assign instr_monitor_if.instr_id            = dut.u_ibex_top.u_ibex_core.id_stage_i.instr_rdata_i;
  assign instr_monitor_if.pc_id               = dut.u_ibex_top.u_ibex_core.pc_id;
  assign instr_monitor_if.branch_taken_id     = dut.u_ibex_top.u_ibex_core.id_stage_i.controller_i.branch_set_i;
  assign instr_monitor_if.branch_target_id    = dut.u_ibex_top.u_ibex_core.branch_target_ex;
  assign instr_monitor_if.stall_id            = dut.u_ibex_top.u_ibex_core.id_stage_i.stall_id;
  assign instr_monitor_if.jump_set_id         = dut.u_ibex_top.u_ibex_core.id_stage_i.jump_set;
  // CSR interface connections
  assign csr_if.csr_access                    = dut.u_ibex_top.u_ibex_core.csr_access;
  assign csr_if.csr_addr                      = dut.u_ibex_top.u_ibex_core.csr_addr;
  assign csr_if.csr_wdata                     = dut.u_ibex_top.u_ibex_core.csr_wdata;
  assign csr_if.csr_rdata                     = dut.u_ibex_top.u_ibex_core.csr_rdata;
  assign csr_if.csr_op                        = dut.u_ibex_top.u_ibex_core.csr_op;

  initial begin
    // Drive the clock and reset lines. Reset everything and start the clock at the beginning of
    // time
    ibex_clk_if.set_active();
    fork
      ibex_clk_if.apply_reset(.reset_width_clks (100));
    join_none

    uvm_config_db#(virtual clk_rst_if)::set(null, "*", "clk_if", ibex_clk_if);
    uvm_config_db#(virtual core_ibex_dut_probe_if)::set(null, "*", "dut_if", dut_if);
    uvm_config_db#(virtual core_ibex_instr_monitor_if)::set(null,
                                                            "*",
                                                            "instr_monitor_if",
                                                            instr_monitor_if);
    uvm_config_db#(virtual core_ibex_csr_if)::set(null, "*", "csr_if", csr_if);
    uvm_config_db#(virtual core_ibex_rvfi_if)::set(null, "*", "rvfi_if", rvfi_if);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*data_if_response*", "vif", data_mem_vif);
    uvm_config_db#(virtual ibex_mem_intf)::set(null, "*instr_if_response*", "vif", instr_mem_vif);
    uvm_config_db#(virtual irq_if)::set(null, "*", "vif", irq_vif);
    run_test();
  end

endmodule
