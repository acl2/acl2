module top (input a);

   wire clk;

   clocking myclocking @(clk);
      input b; // oops, b isn't declared
   endclocking

endmodule
