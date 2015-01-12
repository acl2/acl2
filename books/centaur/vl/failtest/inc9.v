
module top ();

  logic [3:0] w1;
  logic [3:0] w2;

  initial begin
    w2 = (++w1)++;  // ++w1 isn't an lvalue, so you can't increment it
  end


endmodule

