#include <ac_int.h>

// RAC begin

typedef ac_int<14, true> si14;
typedef ac_int<28, true> si28;
typedef ac_int<8, false> ui8;
typedef ac_int<8, true> si8;

int bar() {
  si14 a = 2;
  si28 b = a * a;
  return 0;
}

int bar3() {
  si14 a = 2;
  si28 b = a * a * a;
  return 0;
}

int bar2() {
  si14 a = 3;
  si14 b = a * a;
  si28 b2 = b;
  return 0;
}

int aaa(ui8 e) {
  si8 a = e;
  a = ~a;
  return a;
}

int bbbb(int b, int x2v) {
  ac_int<11, false> p2a = b;
  ac_int<13, false> p2b = x2v;
  ac_int<22, false> prodb = p2a * p2b;
  return 0;
}

// RAC end
