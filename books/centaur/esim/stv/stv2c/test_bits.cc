// ESIM Symbolic Hardware Simulator
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// test_bits.cc -- Tests of bit<n> datatype
//
// Original authors: Nikhil Patil <npatil@centtech.com>
//                   Jared Davis <jared@centtech.com>

#include "bits.h"
#include "fourval.h"
#include <iostream>
#include <cstdlib>

using namespace std;

void test_bit_twiddling();
void test_four_valued();

int main()
{
    auto val = bit<666>::zero();
    val.setBit(109).setBit(9).setBit(8);
    printf("%d %d %d\n", val.getBit(9), val.getBit(8), val.getBit(109));

    test_bit_twiddling();
    test_four_valued();
}

void test_bit_twiddling()
{
    auto x1 = bit<1>::zero();
    assert(x1.getBit(0) == false);
    x1.setBit(0);
    assert(x1.getBit(0) == true);
    x1.clrBit(0);
    assert(x1.getBit(0) == false);
    x1.cpyBit(0, true);
    assert(x1.getBit(0) == true);
    x1.cpyBit(0, false);
    assert(x1.getBit(0) == false);

    auto x2 = bit<2>::zero();
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == false);
    x2.setBit(0);
    assert(x2.getBit(0) == true);
    assert(x2.getBit(1) == false);
    x2.clrBit(0);
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == false);
    x2.cpyBit(0, true);
    assert(x2.getBit(0) == true);
    assert(x2.getBit(1) == false);
    x2.cpyBit(0, false);
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == false);
    x2.setBit(1);
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == true);
    x2.clrBit(1);
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == false);
    x2.cpyBit(1, true);
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == true);
    x2.cpyBit(1, false);
    assert(x2.getBit(0) == false);
    assert(x2.getBit(1) == false);

    auto x8 = bit<8>::zero();
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == false);
    x8.setBit(0);
    assert(x8.getBit(0) == true);
    assert(x8.getBit(7) == false);
    x8.clrBit(0);
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == false);
    x8.cpyBit(0, true);
    assert(x8.getBit(0) == true);
    assert(x8.getBit(7) == false);
    x8.cpyBit(0, false);
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == false);
    x8.setBit(7);
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == true);
    x8.clrBit(7);
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == false);
    x8.cpyBit(7, true);
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == true);
    x8.cpyBit(7, false);
    assert(x8.getBit(0) == false);
    assert(x8.getBit(7) == false);

    auto x3 = bit<19>::zero();
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == false);
    x3.setBit(0);
    assert(x3.getBit(0) == true);
    assert(x3.getBit(17) == false);
    x3.clrBit(0);
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == false);
    x3.cpyBit(0, true);
    assert(x3.getBit(0) == true);
    assert(x3.getBit(17) == false);
    x3.cpyBit(0, false);
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == false);
    x3.setBit(17);
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == true);
    x3.clrBit(17);
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == false);
    x3.cpyBit(17, true);
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == true);
    x3.cpyBit(17, false);
    assert(x3.getBit(0) == false);
    assert(x3.getBit(17) == false);


    auto x4 = bit<203>::zero();
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == false);
    x4.setBit(0);
    assert(x4.getBit(0) == true);
    assert(x4.getBit(155) == false);
    x4.clrBit(0);
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == false);
    x4.cpyBit(0, true);
    assert(x4.getBit(0) == true);
    assert(x4.getBit(155) == false);
    x4.cpyBit(0, false);
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == false);
    x4.setBit(155);
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == true);
    x4.clrBit(155);
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == false);
    x4.cpyBit(155, true);
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == true);
    x4.cpyBit(155, false);
    assert(x4.getBit(0) == false);
    assert(x4.getBit(155) == false);
}


void test_four_valued()
{
    auto x1 = fourval<1>::all_0();
    assert(x1.onset.getBit(0) == false);
    assert(x1.offset.getBit(0) == true);
    assert(x1.isPureBoolean());
    cout << x1 << endl;

    auto x2 = fourval<2>::all_0();
    assert(x2.onset.getBit(0) == false);
    assert(x2.offset.getBit(0) == true);
    assert(x2.isPureBoolean());
    cout << x2 << endl;

    auto x3 = fourval<20>::all_0();
    assert(x3.onset.getBit(0) == false);
    assert(x3.offset.getBit(0) == true);
    assert(x3.isPureBoolean());
    cout << x3 << endl;

    auto x4 = fourval<23>::all_0();
    assert(x4.onset.getBit(0) == false);
    assert(x4.offset.getBit(0) == true);
    assert(x4.isPureBoolean());
    cout << "all zeros: " << x4 << endl;

    auto x5 = fourval<23>::all_1();
    assert(x5.onset.getBit(0) == true);
    assert(x5.offset.getBit(0) == false);
    assert(x5.isPureBoolean());
    cout << "all ones: " << x5 << endl;

    auto x6 = fourval<23>::all_X();
    assert(x6.onset.getBit(0) == true);
    assert(x6.offset.getBit(0) == true);
    assert(!x6.isPureBoolean());
    cout << "all xes: " << x6 << endl;

    auto x7 = fourval<23>::all_Z();
    assert(x7.onset.getBit(0) == false);
    assert(x7.offset.getBit(0) == false);
    assert(!x7.isPureBoolean());
    cout << "all zes: " << x7 << endl;


}
