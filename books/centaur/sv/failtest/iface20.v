// NCVerilog tolerates this, but VCS rejects it, saying that
// modports can only be specified for interface instances, ports, or variables,
// but cannot be specified for a port or variable of a modport type.

interface myiface ();

  logic [2:0] item;

  modport producer (output item);
  modport consumer (input item);

endinterface

module myconsumer1 (myiface.consumer iface) ;

endmodule

module myconsumer2 (myiface.consumer iface) ;

  myconsumer1 inst (.iface(iface.consumer));   // oops, can't use .consumer here because iface is a port

endmodule

module top ;

  myiface iface();

  myconsumer2 cs ( .iface(iface) );

endmodule
