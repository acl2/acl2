
module top ();

  parameter version = 1;
  wire [127:0] in;

  if (version == 0)
  begin : foo
    wire bar = in[0];
  end
  else if (version == 1)
     wire [3:0] xxx = in[3:0];
  else
     wire [3:0] foo = in[13:10];

  if (version == 0)
      logic [3:0] yyy = in[3:0];
  else if (version == 1)
  begin : foo                     // oops, name "foo" used above
    wire [3:0] yyy = in[7:4];
  end
  else ;


endmodule
