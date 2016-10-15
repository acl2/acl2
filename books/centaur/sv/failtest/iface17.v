interface myiface ();

  logic [2:0] item;

  modport producer (output item);
  modport consumer (input item);

endinterface

module myconsumer (myiface.consumer iface) ;

endmodule

module top ;

  myiface iface();

  myconsumer cs ( .iface(iface.producer) );  // oops, should be iface.consumer

endmodule
