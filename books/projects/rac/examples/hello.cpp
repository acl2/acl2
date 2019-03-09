// One of the simplest possible RAC programs

// arbitrary C++

#include <iostream>
#include <ac_int.h>
#include <rac.h>
using namespace std;

// RAC begin
// In this section, only RAC code is acceptable

typedef ac_int<8,false> ui8;
typedef ac_int<16,false> ui16;
typedef ac_int<8,true> si8;

ui8 reverseByte(ui8 mumble)
{
  ui8 result;

  for(int i=0; i<4; i++) {
    result.set_slc(2*i, mumble.slc<2>(6-2*i));
  }

  return result;
}

// RAC end

// arbitrary C++

int main (int argc, char *argv[]) {

  ui8 a_byte;
  ui8 another_byte;
  unsigned int in;

  while (! cin.eof()) {

    cin >> hex >> in;
    a_byte = in;

    another_byte = reverseByte (a_byte);

    cout << hex << a_byte.to_uint() << " --> " << another_byte.to_uint() << endl;

  }

  return 0;
}

