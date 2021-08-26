#include <stdio.h>

int main(void) {
  int a = 3;
  int b = -2;
  unsigned int r = one(a, b);
  unsigned int s = two(b, a);
  printf("one(%d, %d) = %d\n", a, b, r);
  printf("two(%d, %d) = %d\n", b, a, s);
}
