


module spec (input logic [127:0] in,
	     output logic [127:0] out);


  wire [3:0] a;
  wire signed [3:0] b;

  wire a1 = a ==? 6'b??1??0;
  wire a2 = a !=? 6'b??1??0;
  wire a3 = a ==? 6'b001??0;
  wire a4 = a !=? 6'b001??0;
  wire a5 = a ==? 6'b111??0;
  wire a6 = a !=? 6'b111??0;
  wire a7 = a ==?   4'b1??0;
  wire a8 = a !=?   4'b1??0;

  wire b1 = b ==? 6'b??1??0;
  wire b2 = b !=? 6'b??1??0;
  wire b3 = b ==? 6'b001??0;
  wire b4 = b !=? 6'b001??0;
  wire b5 = b ==? 6'b111??0;
  wire b6 = b !=? 6'b111??0;
  wire b7 = b ==?   4'b1??0  ;
  wire b8 = b !=?   4'b1??0  ;

   assign a = in;
   assign b = in;
   assign out = {a1, a2, a3, a4, a5, a6, a7, a8,
                 b1, b2, b3, b4, b5, b6, b7, b8 };

endmodule
