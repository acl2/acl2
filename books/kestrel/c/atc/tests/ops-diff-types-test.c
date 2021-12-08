#include <stdio.h>

int main(void) {
  unsigned int x = 3;
  unsigned char y = 77;
  unsigned int r = f(x, y);
  printf("f(%d, %d) = %d\n", x, y, r);
}
