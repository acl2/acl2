

`define show(x) $display(`"x: %b`", x)


module test ();
  logic [31:0] in;
  logic [8:0] out1;
  logic [6:0] out2;
   assign {<< 5 {{<< 3 {out1}}, out2}} = in[31:0];

  logic [8:0] guess1;
  logic [6:0] guess2;
 logic [31:0] temp1;
 logic [15:0] temp2;
 logic [8:0] temp3;
 logic [6:0] temp4;
 assign temp1 = {<< 5 {in[31:0]}};
 assign temp2 = temp1 >> 16;
 assign {temp3, temp4} = temp2;
 assign guess2 = temp4;
 assign guess1 = {<< 3 {temp3}};

  // logic [8:0] guess1;
  // logic [8:0] intermed;
  // logic [6:0] guess2;
  // logic [15:0] padding;
  // logic [31:0] revrev;
  //  assign {>> {{<< 3 {guess1}}, guess2, padding}} = {<< 5 {in[31:0]}};
  //  // assign {intermed, guess2, padding} = {<< 5 {in[31:0]}};
  //  // assign guess1 = {<< 3 {intermed}};

   initial begin
     for (integer i=0; i<32; i++) begin
       in = 1<<i;
       #1;
       $display("i=%d: out1 %b, out2 %b, guess1 %b, guess2 %b, ok %b", i, out1, out2, guess1, guess2, out1 == guess1 && out2 == guess2);
       // `show(in);
//       `show(out);
  //     `show(guess);
     end
   end
endmodule
