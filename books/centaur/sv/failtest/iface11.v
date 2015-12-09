module mybuf (output out, input in);

  assign out = in;

endmodule

interface simplebus ;

  wire myout, myin;

  mybuf mybuf_inst (myout, myin);  // oops, not allowed to instantiate modules in interfaces (definitely)
  //   - interfaces are explicitly prohibited from having module instances (25.3, page 713)

endinterface

module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule

