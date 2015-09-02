// One of the simplest possible MASC SystemC files

#include <systemc.h>
#include <masc.h>

// arbitrary C++

// Masc begin
// In this section, only Masc code is acceptable

typedef sc_uint<8> ui8;

ui8 reverseByte(ui8 mumble)
{
  ui8 result;

  for(int i=0; i<4; i++) {
    // CtoS: i in {0,1,2,3}
    result.range(2*i+1,2*i) = mumble.range(7-2*i, 6-2*i);
  }

  return result;
}

// Masc end

// arbitrary C++

int sc_main (int argc, char *argv[]) {

  ui8 a_byte;
  ui8 another_byte;

  while (! cin.eof()) {

    cin >> a_byte;

    another_byte = reverseByte (a_byte);

    cout << a_byte << " --> " << another_byte << endl;

  }

  return 0;
}

/*
Notes

compiled with g++ -I /p/dt/fvcoe/pub/tools/SystemC/systemc-2.3.0/include -L /p/dt/fvcoe/pub/tools/SystemC/systemc-2.3.0/lib-linux64/ -lsystemc hello.cpp

look to find out if there's an env var to tell g++ to add -I and -L flags
under the hood.

Parser feature requests:

0) Print some helpful text.

   Want:

     % parse
     Usage:
       parse file.cpp      check that file.cpp is "in the subset"
       parse file.cpp output.cpp     generate CtoS-able code in output.cpp
       parse -acl2 file.cpp output.lsp   not implemented yet

1) Want: MASC code can be intermixed with C++.

Start of MASC code is indicated by this comment all alone on a line:

// m a s c: begin

End of MASC code is similarly indicated:


// m a s c: end

Outside of Masc begin/end region you can have any arbitrary C++ code.
This is used above to add some standard includes (e.g. #include <systemc.h>)
at the top of file and a very lightweight testbench at the bottom.

parser drops the non-masc code and only translates the masc code.
same for pretty printer.


*/
