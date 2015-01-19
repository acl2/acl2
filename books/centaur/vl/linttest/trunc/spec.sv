

module dut;

  wire clk;
  wire [3:0] foo;
  wire [2:0] trunc1, trunc2, trunc3, trunc4, trunc5, trunc6, trunc7, trunc8;

  assign trunc1 = foo;
  assign trunc2 = (foo & 4'b0);

  always_comb
  begin
    trunc3 = foo;
    trunc4 = (foo & 4'b0);
  end

  always @(posedge clk)
  begin
    trunc5 <= foo;
    trunc6 <= (foo & 4'b0);
  end

  always_ff @(posedge clk)
  begin
    trunc7 <= foo;
    trunc8 <= (foo & 4'b0);
  end

  function [2:0] truncfun (logic [3:0] i) ;
    logic [2:0] trunc9;
    begin
      trunc9 = i;
      truncfun = i;
    end
  endfunction

  task trunctask (output [2:0] trunc10, input [3:0] i) ;
    logic [2:0] trunc11;
    begin
      trunc10 = i;
      trunc11 = i;
    end
  endtask

  logic [2:0] trunc12, trunc13;

  initial begin
    trunc12 = foo;
    trunc13 = (foo & 4'b0);
  end

  genvar i;
  wire [9:0][2:0] warr;
  generate
    for(i = 0;i < 10;++i) begin
      assign warr[i] = foo;
    end
  endgenerate

endmodule
