#include <stdio.h>

#include "not.h"

int main(void) {
  int a = 3;
  int b = -2;
  unsigned int r = one(a);
  unsigned int s = two(b, a);
  printf("one(%d) = %d\n", a, r);
  printf("two(%d, %d) = %d\n", b, a, s);
  return 0;
}
