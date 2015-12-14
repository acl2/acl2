
interface simplebus ;

  wire myout, myin;

  buf mybuf_inst (myout, myin);  // oops, not allowed to instantiate gates in interfaces (probably)

  // I can't point to anywhere in the SystemVerilog standard that says
  // you can't do this.
  //   - But I don't think I see a way to have them according to the grammar.
  //   - And you're definitely explicitly prohibited from having module instances (25.3, page 713)
  //   - And they're not allowed by VCS or NCVerilog.

endinterface

module top (output topout, input topin);

  wire foo;

  simplebus sb ();

endmodule

