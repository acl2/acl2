module top (input a);

   clocking myclocking (a); // oops, should be @(a)

   endclocking

endmodule
