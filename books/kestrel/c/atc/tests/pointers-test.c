#include <stdio.h>

#include "pointers.h"

void f1_test() {
  int x = -3;
  int r = f1(&x);
  printf("f1(%d) = %d\n", x, r);
}

void f2_test() {
  unsigned int a = 18;
  unsigned int b = 2;
  int r = f2(&a, &b);
  printf("f2(%d, %d) = %d\n", a, b, r);
}

void g1_test() {
  signed long long a = 88888888888;
  signed long long r = g1(&a);
  printf("g1(%lld) = %lld\n", a, r);
}

void g2_test() {
  signed long long a = 88888888888;
  g2(&a);
  printf("g2(%lld)\n", a);
}

void g3_test() {
  signed long long a = 88888888888;
  int r = g3(&a);
  printf("g3(%lld) = %d\n", a, r);
}

void h1_test() {
  unsigned short n = 180;
  unsigned short e = 200;
  printf("n = %d\n", n);
  h1(&n, e);
  printf("n = %d\n", n);
}

void h2_test() {
  unsigned int e = 10;
  unsigned int m = 20;
  printf("m = %d\n", m);
  h2(e, &m);
  printf("m = %d\n", m);
}

void swap_uints_test() {
  unsigned int a = 10;
  unsigned int b = 20;
  swap_uints(&a, &b);
  printf("a = %d\n", a);
  printf("b = %d\n", b);
}

int main(void) {
  f1_test();
  f2_test();
  g1_test();
  g2_test();
  g3_test();
  h1_test();
  h2_test();
  swap_uints_test();
  return 0;
}
