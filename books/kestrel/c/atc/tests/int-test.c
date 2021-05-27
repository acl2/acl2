#include <stdio.h>

int main(void) {
  int x = 3;
  int y = -2;
  int z = 8;
  int r = f(x, y, z);
  printf("f(%d, %d, %d) = %d\n", x, y, z, r);
}
