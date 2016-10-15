interface myiface ();

  logic [2:0] item;

  modport producer (output item);
  modport consumer (input item);

endinterface

module myconsumer (myiface.consumer iface) ;

endmodule

module middleman () ;

  myconsumer cs ( .iface(top.iface) );  // oops, top.iface doesn't exist

endmodule

module top ;

  middleman themiddleman();

endmodule
