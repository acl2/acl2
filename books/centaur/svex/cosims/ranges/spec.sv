
module spec (input logic [127:0] in,
	     output logic [127:0] out);


  wire [3:7] a;
  wire [7:3] b;
  wire [3:3] c;

  assign {a, b, c} = in;

  assign out = {  a[4:6],
                  a[4:4],
                  a[1:6],
                  a[4:9],
		  a[1:2],
		  a[8:9],

                  b[6:4],
                  b[4:4],
                  b[6:1],
                  b[9:4],
		  b[2:1],
		  b[9:8],

                  c[3:3],

                  c[2:1],
                  c[4:4],
                  c[6:1],
                  c[9:4]

		  // NCverilog gets a lot of this wrong.
		  // VCS rejects the following selects.
                  // c[4:6],
                  // c[4:4],
                  // c[1:6],
                  // c[4:9]
		  };

endmodule // spec
