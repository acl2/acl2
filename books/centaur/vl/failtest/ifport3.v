interface tricky;
  logic [2:0] foo_t;
endinterface

module top ;
  tricky.foo_t a;
endmodule
