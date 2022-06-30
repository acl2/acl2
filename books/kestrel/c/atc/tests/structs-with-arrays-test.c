#include <stdio.h>

struct scalar_and_array { // copied from structs-with-arrays.c
    int scalar;
    unsigned char aggreg[10];
};

void test_read_from_scalar_and_array() {
  struct scalar_and_array sar =
    {.scalar = 8, .aggreg = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}};
  int a = read_scalar(&sar);
  int b = read_aggreg(5, &sar);
  printf("a = %d\nb = %d\n", a, b);
}

void test_write_to_scalar_and_array() {
  struct scalar_and_array sar =
    {.scalar = 8, .aggreg = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}};
  write_scalar(80, &sar);
  write_aggreg(5, 50, &sar);
  int a = read_scalar(&sar);
  int b = read_aggreg(5, &sar);
  printf("a = %d\nb = %d\n", a, b);
}

int main(void) {
  test_read_from_scalar_and_array();
  test_write_to_scalar_and_array();
  return 0;
}
