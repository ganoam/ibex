// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_fcov_bind;
  bind core_ibex_tb_top.dut.u_ibex_cc.u_ibex_core core_ibex_fcov_if u_fcov_bind (
    .*
  );
endmodule
