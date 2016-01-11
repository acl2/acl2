
interface alu_iface ();
  logic [3:0] a;
  logic [3:0] b;
  logic [3:0] op;
  logic [3:0] out1;
  modport unit1(input op, a, b, output out1);
endinterface


module top ;

  for(genvar i = 0; i < 4; ++i)
  begin: foo
    alu_iface aluif();
  end

  alu1 myalu ( .aif(foo[0].aluif) ); // oops, too hard for NCV and VCS.

  // It seems like this should probably be legal, but you can't really follow
  // this hierarchical reference before elaboration.

  // VCS Version J-2014.12-SP3-1 fails with:

  //    Error-[ELAB-ICIP] Illegally connected interface port
  //    iface23.v, 18
  //    "alu1 myalu( .aif (foo[0].aluif));"
  //      The interface port 'aif' of module 'alu1' whose type is interface 
  //      'alu_iface' is illegally connected.  An unresolved or generated instance 
  //      name 'foo[0].aluif' is used.
  //      Please make sure that all ports are properly connected.

  // NCVerilog 15.10-s008 reports:

  //   alu1 myalu ( .aif(foo[0].aluif) ); // oops, too hard for NCV and VCS.
  //                                |
  // ncelab: *E,CUIOAI (./iface23.v,18|31): Illegal interface port connection through a
  //         generate or array instance (top.foo[0].aluif) .
  // module alu1 (alu_iface aif);
  //                          |

endmodule


module alu1 (alu_iface aif);

endmodule

