// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Package with common parameters used by the Ibex Core Complex
 */

// TODO: Probably will remain unused.
package ibex_cc_pkg;

parameter int  XInterfaceNumHier    = 0;
parameter int  XInterfaceNumRsp     = '{0};
parameter bit  XInterfaceTernaryOps = 1'b0;
parameter bit  XInterfaceDualWriteback     = 1'b0;


parameter type acc_c_req_t          = logic;
parameter type acc_c_rsp_t          = logic;



endpackage
