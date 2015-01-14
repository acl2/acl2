interface tricky;
  logic [2:0] foo_t;
endinterface

module top (output topout, input topin);
  tricky.foo_t a;
endmodule
