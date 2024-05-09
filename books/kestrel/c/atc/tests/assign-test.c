#include <stdio.h>

#include "assign.h"

void test_f() {
  int x = 7733;
  int y = -939;
  int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}

void test_g() {
  int a = 88;
  int b = -4400;
  int r = g(a, b);
  printf("g(%d, %d) = %d\n", a, b, r);
}

void test_h() {
  int x = 77839;
  int y = -2828;
  int z = 4;
  int r = h(x, y, z);
  printf("h(%d, %d, %d) = %d\n", x, y, z, r);
}

void test_i() {
  int p = 10;
  int q = 20;
  int r = i(p, q);
  printf("i(%d, %d) = %d\n", p, q, r);
}

void test_j() {
  int x = 3382932;
  int r = j(x);
  printf("j(%d) = %d\n", x, r);
}

void test_k() {
  int x = -282882;
  int y = -811111;
  int r = k(x, y);
  printf("k(%d, %d) = %d\n", x, y, r);
}

void test_l() {
  unsigned int x = 1000000;
  unsigned int r = l(x);
  printf("l(%d) = %d\n", x, r);
}

int main(void) {
  test_f();
  test_g();
  test_h();
  test_i();
  test_j();
  test_k();
  test_l();
  return 0;
}
