interface myiface ();

  logic [2:0] item;

  modport producer (output item);
  modport consumer (input item);

endinterface

module myconsumer (myiface.consumer iface) ;

endmodule

module middleman () ;

  myconsumer cs ( .iface(top.iface.consumer) );  // oops, hierarchical reference to non-existing interface

endmodule

module top ;

  middleman themiddleman();

endmodule
