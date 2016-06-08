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

    cout << a_byte.to_uint() << " --> " << another_byte.to_uint() << endl;

  }

  return 0;
}

