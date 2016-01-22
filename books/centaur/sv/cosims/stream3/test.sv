`define show(x) $display(`"x: %b`", x)


module test ();

  logic [3:0] in;
  logic [3:0] out;
   assign {<< 3 {out}} = in;


  logic [3:0] guess1;
   assign { guess1[2:0], guess1[3] } = in;

  logic [3:0] guess2;
   assign { guess2[0], guess2[3:1] } = in;

  logic [3:0] guess3;
   assign guess3 = {in[2:0], in[3]};

  logic [3:0] guess4;
   assign guess4 = {<< 3 {in}};

   // assign { out[0], ??, out[3:1] } = in;

   initial begin
     for (integer i=0; i<5; i++) begin
       in = 1<<i;
       #1;
       $display("out: %b, guess1: %b, guess2: %b, guess3: %b, guess4: %b", out, guess1, guess2, guess3, guess4);
     end
   end
endmodule
