#include <stdio.h>

struct point2D { // copied from structs.c
  int x;
  int y;
};

struct point3D { // copied from structs.c
  int x;
  int y;
  int z;
};

struct scalar_and_array { // copied from structs.c
  int scalar;
  unsigned char aggreg[10];
};

void test_read_from_point2D_by_value() {
  struct point2D point = {.x = 11, .y = 22};
  int x = read_x_from_point2D_by_value(point);
  int y = read_y_from_point2D_by_value(point);
  printf("point = (%d, %d)\n", x, y);
}

void test_read_from_point2D_by_pointer() {
  struct point2D point = {.x = 11, .y = 22};
  int x = read_x_from_point2D_by_pointer(&point);
  int y = read_y_from_point2D_by_pointer(&point);
  printf("point = (%d, %d)\n", x, y);
}

void test_write_to_point2D() {
  struct point2D point = {.x = 11, .y = 22};
  write_x_to_point2D(&point);
  write_y_to_point2D(&point);
  printf("point = (%d, %d)\n", point.x, point.y);
}

void test_allpos_by_value() {
  struct point3D point1 = {.x = 80, .y = 44, .z = 2};
  struct point3D point2 = {.x = 80, .y = -1, .z = 2};
  int yes = allpos_by_value(point1);
  int no = allpos_by_value(point2);
  printf("yes = %d\nno = %d\n", yes, no);
}

void test_allpos_by_pointer() {
  struct point3D point1 = {.x = 80, .y = 44, .z = 2};
  struct point3D point2 = {.x = 80, .y = -1, .z = 2};
  int yes = allpos_by_pointer(&point1);
  int no = allpos_by_pointer(&point2);
  printf("yes = %d\nno = %d\n", yes, no);
}

void test_read_from_scalar_and_array() {
  struct scalar_and_array sar =
    {.scalar = 8, .aggreg = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}};
  int a = read_scalar_by_value(sar);
  int b = read_scalar_by_pointer(&sar);
  int c = read_aggreg_by_value(5, sar);
  int d = read_aggreg_by_pointer(5, &sar);
  printf("a = %d\nb = %d\nc = %d\nd = %d\n", a, b, c, d);
}

void test_write_to_scalar_and_array() {
  struct scalar_and_array sar =
    {.scalar = 8, .aggreg = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}};
  write_scalar(80, &sar);
  write_aggreg(5, 50, &sar);
  int a = read_scalar_by_pointer(&sar);
  int b = read_aggreg_by_pointer(5, &sar);
  printf("a = %d\nb = %d\n", a, b);
}

int main(void) {
  test_read_from_point2D_by_value();
  test_read_from_point2D_by_pointer();
  test_write_to_point2D();
  test_allpos_by_value();
  test_allpos_by_pointer();
  test_read_from_scalar_and_array();
  test_write_to_scalar_and_array();
  return 0;
}
