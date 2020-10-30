#include <stdio.h>

int main(void) {
  int current = 50000;
  int hibyte = 240;
  int lobyte = 15;
  int r = checksum(current, hibyte, lobyte);
  printf("f(%d, %d, %d) = %d\n", current, hibyte, lobyte, r);
}
