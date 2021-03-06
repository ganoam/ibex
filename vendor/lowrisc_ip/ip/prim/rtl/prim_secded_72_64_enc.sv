// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// SECDED Encoder generated by
// util/design/secded_gen.py -m 8 -k 64 -s 1592631616 -c hsiao

module prim_secded_72_64_enc (
  input        [63:0] in,
  output logic [71:0] out
);

  always_comb begin : p_encode
    out = 72'(in);
    out[64] = ^(out & 72'h009D000000001FFFFF);
    out[65] = ^(out & 72'h007600000FFFE0003F);
    out[66] = ^(out & 72'h0079003FF003E007C1);
    out[67] = ^(out & 72'h00A70FC0F03C207842);
    out[68] = ^(out & 72'h00D371C711C4438884);
    out[69] = ^(out & 72'h00F8B65926488C9108);
    out[70] = ^(out & 72'h00AEDAAA4A91152210);
    out[71] = ^(out & 72'h004FED348D221A4420);
  end

endmodule : prim_secded_72_64_enc
