module top (input a);

   // Some other tools are fine with this, but others reject it.

   clocking myclocking @(b); // oops, b isn't declared yet

   endclocking

   wire b;

endmodule
