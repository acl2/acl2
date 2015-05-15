



module ddddeeee #(parameter dw = 64, aw = 6)
               (output logic [aw-1:0] out,
                input  logic [dw-1:0]    d); 


function [aw:0] eeeee;
  input [dw-1:0]  D;
  reg [aw:0]   temp;
  reg done;
  integer i;

  begin
    done = 0;
    temp = {aw+1{1'b1}};
    temp = D[dw-1] == 1'b1;
    eeeee = temp;
// synopsys translate_on
  end
endfunction // eeeee


function [dw-1:0] ddddd;

  input [dw-1:0]  D;
  reg [aw:0]   temp_enc;
  reg [dw-1:0]    temp_dec;

  begin
    temp_enc = eeeee(D);
    temp_dec = {dw{1'b0}};

    ddddd = temp_dec ^ temp_enc;
  end
endfunction // ddddd

 
logic [aw:0] foo;

   assign foo = ddddd(d);

   assign out = foo;
endmodule // ddddeeee


module spec (input logic [127:0] in,
	     output [127:0] out);

   ddddeeee         inst1 (.d(in[63:0]), .out(out[5:0]));

   ddddeeee #(16,4) inst2 (.d(in[15:0]), .out(out[9:6]));

endmodule // spec

