
module top ();

  // SystemVerilog-2012 page 80, Table 6-10
  //   "N shall be a positive integral number"

  typedef enum logic [3:0] {
    foo,
    bar[0],  // Oops, not OK
    baz
  } mytype_t;

endmodule
