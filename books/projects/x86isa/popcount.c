// From Sean Anderson's Bit Twiddling Hacks
// See https://graphics.stanford.edu/~seander/bithacks.html

#include <stdio.h>
#include <stdlib.h>

int popcount_32(unsigned int v) {
  v = v - ((v >> 1) & 0x55555555);
  v = (v & 0x33333333) + ((v >> 2) & 0x33333333);
  v = ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
  return (v);
}

int main(int argc, char *argv[], char *env[]) {
  int v;
  printf("\nEnter a 32-bit number: ");
  scanf("%d", &v);
  v = v & 0xffffffff;
  printf("\nPopcount of %d is: %d\n", v, popcount_32(v));
  return 0;
}
