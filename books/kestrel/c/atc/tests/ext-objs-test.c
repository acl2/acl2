#include <stdio.h>

#include "ext-objs.h"

int main(void) {
  int a = f(2);
  printf("a = %d\n", a);
  int b = g();
  printf("b = %d\n", b);
  h(2);
  int a1 = f(2);
  printf("a1 = %d\n", a1);
  i();
  printf("arr2[0] = %d\n", arr2[0]);
  return 0;
}
