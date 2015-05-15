










module spec (input logic [127:0] in,
	     output wire [127:0] out);

  integer a;
   always_comb begin
     case (in[2:0])
       0:       a = 0;
       1, 2, 3: a = 1;
       4, 5, 6: a = 2;
       7:       a = 3;
       default: a = 4;
     endcase // case (in[2:0])
   end

  integer b;
   always_comb begin
     casez (in[5:3])
       3'b00? :    b = 0;
       3'b0?1 :    b = 1;
       3'b?10 :    b = 2;
       3'b1?? :    b = 3;
       default:    b = 4;
     endcase // casez (in[5:3])
   end

   assign out = {b, a};

endmodule // spec
