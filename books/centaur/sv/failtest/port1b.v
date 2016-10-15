interface IFoo;
  logic [3:0] status;
endinterface

interface IBar;
  logic [3:0] status;
endinterface

module top (output topout, input topin);

  IFoo thefoo();
  IBar thebar();

  sub1 mysub(thefoo, thebar);

endmodule

module sub1 (IFoo thefoo, IBar thebar) ;

  sub2 mysub2 (thebar, thefoo);  // oops, wrong order

endmodule

module sub2 (IFoo thefoo, IBar thebar) ;

endmodule
