#include <stdio.h>

int legacy(int current, int hibyte, int lobyte);

unsigned int checksum(unsigned int current, unsigned char hibyte, unsigned char lobyte);

void test_legacy() {
  int current = 50000;
  int hibyte = 240;
  int lobyte = 15;
  int r = legacy(current, hibyte, lobyte);
  printf("legacy(%d, %d, %d) = %d\n", current, hibyte, lobyte, r);
}

void test_checksum() {
  int current = 50000;
  unsigned char hibyte = 240;
  unsigned char lobyte = 15;
  int r = checksum(current, hibyte, lobyte);
  printf("checksum(%d, %d, %d) = %d\n", current, hibyte, lobyte, r);
}

int main(void) {
  test_legacy();
  test_checksum();
  return 0;
}
