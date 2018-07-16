module top (input a);

   wire clk;
   wire c;

   clocking @(clk);  // oops, non-default clocking block needs a name
      input b = c;
   endclocking

endmodule
