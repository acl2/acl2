interface IFoo;
  logic [3:0] status;
endinterface

interface IBar;
  logic [3:0] status;
endinterface

module top (output topout, input topin);

  IFoo thefoo();
  IBar thebar();

  sub mysub(thebar, thefoo);   // oops, wrong argument order

endmodule

module sub (IFoo thefoo, IBar thebar) ;

endmodule
