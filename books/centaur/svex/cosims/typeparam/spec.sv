



module negatory #(parameter width = 1, type DTYPE=logic)
   (output DTYPE [width-1:0] q,
    input DTYPE [width-1:0] d);

   assign q = ~d;

endmodule

typedef logic[3:0] foo_t;

typedef struct packed { foo_t [3:1] bar; logic [1:5] baz; } fuz_t;

module spec (input logic [127:0] in,
	     output wire [127:0] out);


   fuz_t [3:0] a, na;
   foo_t b, nb;
  struct packed { fuz_t a; foo_t b; } [1:0] c, nc;

   assign {c, b, a} = in;
   assign out = {nc, nb, na};

   negatory #(.width(4), .DTYPE(fuz_t)) ainst(na, a);
   negatory #(.width(1), .DTYPE(foo_t)) binst(nb, b);
   negatory #(.width(2), .DTYPE(struct packed { fuz_t a; foo_t b; })) cinst(nc, c);



endmodule
