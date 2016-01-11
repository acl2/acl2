interface iface ();

  logic [2:0] item;

  // I don't know whether this is supposed to work, but:
  //
  //  - NCVerilog errors and says that modport declarations are only allowed
  //    in interface declarations.
  //
  //  - VCS errors and says Modports inside generates are not supported.

  begin: foo
    modport producer (output item);
  end

endinterface


module sub (iface myiface) ;

endmodule


module top ;

  iface myiface ();

  sub mysub (myiface);

endmodule



