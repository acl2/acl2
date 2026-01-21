/*
  License: (An MIT/X11-style license)

   Permission is hereby granted, free of charge, to any person obtaining a
   copy of this software and associated documentation files (the "Software"),
   to deal in the Software without restriction, including without limitation
   the rights to use, copy, modify, merge, publish, distribute, sublicense,
   and/or sell copies of the Software, and to permit persons to whom the
   Software is furnished to do so, subject to the following conditions:

   The above copyright notice and this permission notice shall be included in
   all copies or substantial portions of the Software.

   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
   DEALINGS IN THE SOFTWARE.

 Original author: Mayank Manjrekar <mayank.manjrekar2@arm.com>
*/

#include <stdio.h>
#include <math.h>
#include <string>
#include <vector>

#ifdef SLEC
#include "rac.h"
#else
#include <tuple>
#endif

#include "ac_int.h"

#define DBG(X) std::cout << (#X) << ": " << X.to_string(AC_HEX) << '\n';
#define DBGB(X) std::cout << (#X) << ": " << X << '\n';

using namespace std;

#ifdef SLEC

#include "ac_probe.h"

#else

namespace ac {
  template <typename T>
  void probe_map(const char*prbnm, T inp) {}
}

#endif

// RAC begin

typedef ac_int<8, false> ui8;
typedef ac_int<16, false> ui16;

// Compression tree from the
ui16 compress(ui16 pp0, ui16 pp1, ui16 pp2, ui16 pp3, ui16 pp4, ui16 pp5, ui16 pp6, ui16 pp7) {
  ui16 l0pp0 = pp0 ^ pp1 ^ pp2;
  ui16 l0pp1 = ((pp0 & pp1) | (pp0 & pp2) | (pp1 & pp2)) << 1;
  ui16 l0pp2 = pp3 ^ pp4 ^ pp5;
  ui16 l0pp3 = ((pp3 & pp4) | (pp3 & pp5) | (pp4 & pp5)) << 1;
  ui16 l0pp4 = pp6;
  ui16 l0pp5 = pp7;

  ui16 l1pp0 = l0pp0 ^ l0pp1 ^ l0pp2;
  ui16 l1pp1 = ((l0pp0 & l0pp1) | (l0pp0 & l0pp2) | (l0pp1 & l0pp2)) << 1;
  ui16 l1pp2 = l0pp3 ^ l0pp4 ^ l0pp5;
  ui16 l1pp3 = ((l0pp3 & l0pp4) | (l0pp3 & l0pp5) | (l0pp4 & l0pp5)) << 1;

  ui16 l2pp0 = l1pp0 ^ l1pp1 ^ l1pp2;
  ui16 l2pp1 = ((l1pp0 & l1pp1) | (l1pp0 & l1pp2) | (l1pp1 & l1pp2)) << 1;
  ui16 l2pp2 = l1pp3;

  ui16 l3pp0 = l2pp0 ^ l2pp1 ^ l2pp2;
  ui16 l3pp1 = ((l2pp0 & l2pp1) | (l2pp0 & l2pp2) | (l2pp1 & l2pp2)) << 1;

  return l3pp0 + l3pp1;
}

array<ui16, 8> genPP(ui8 a, ui8 b) {
  array<ui16, 8> pp;
  for (uint i=0; i<8; i++) {
    pp[i] = 0;
    pp[i].set_slc(i, a[i] ? b : ui8(0));
  }
  return pp;
}

ui16 computeProd(ui8 a, ui8 b) {
  array<ui16, 8> pp = genPP(a, b);

  return compress(pp[0], pp[1], pp[2], pp[3], pp[4], pp[5], pp[6], pp[7]);
}

// RAC end

int main() {
  ui8 a = 3;
  ui8 b = 5;
  ui16 sum = computeProd(a, b);

  DBG(sum);
}
