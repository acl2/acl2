interface foo (bar thebar) ;

endinterface

interface bar () ;

endinterface

module top ;

  foo myfoo (mybar); //  <-- creates an implicit wire (but not an implicit interface)
  bar mybar ();      // hence this is a name clash

endmodule
