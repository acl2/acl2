// I'm not sure if this rule is written down anywhere, but NCVerilog and VCS
// both reject this.

interface myiface ();

  logic [2:0] item;

  modport producer (output item);
  modport consumer (input item);

endinterface

module myconsumer (myiface.consumer iface) ;

endmodule

module middleman () ;

  myconsumer cs ( .iface(top.iface) );  // oops, can't use interface from another module

endmodule

module top ;

  middleman themiddleman();

endmodule
