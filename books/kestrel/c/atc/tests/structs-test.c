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

struct flex { // copied from structs.c
    unsigned char fixed[5];
    unsigned int filler;
    unsigned char last[];
};

// without these, we get a type error
// because the compiler thinks that these two functions return int
// (eventually ATC should also generate a .h file,
// which then this test file can include):
struct point2D write_x_to_point2D_by_value(struct point2D point);
struct point2D write_y_to_point2D_by_value(struct point2D point);
struct scalar_and_array write_scalar_by_value(int v, struct scalar_and_array a);
struct scalar_and_array write_aggreg_by_value(int i, unsigned char v, struct scalar_and_array a);

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

void test_write_to_point2D_by_value() {
  struct point2D point = {.x = 11, .y = 22};
  point = write_x_to_point2D_by_value(point);
  point = write_y_to_point2D_by_value(point);
  printf("point = (%d, %d)\n", point.x, point.y);
}

void test_write_to_point2D_by_pointer() {
  struct point2D point = {.x = 11, .y = 22};
  write_x_to_point2D_by_pointer(&point);
  write_y_to_point2D_by_pointer(&point);
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

void test_write_to_scalar_and_array_by_value() {
  struct scalar_and_array sar =
    {.scalar = 8, .aggreg = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}};
  sar = write_scalar_by_value(80, sar);
  sar = write_aggreg_by_value(5, 50, sar);
  int a = read_scalar_by_value(sar);
  int b = read_aggreg_by_value(5, sar);
  printf("a = %d\nb = %d\n", a, b);
}

void test_write_to_scalar_and_array_by_pointer() {
  struct scalar_and_array sar =
    {.scalar = 8, .aggreg = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}};
  write_scalar_by_pointer(80, &sar);
  write_aggreg_by_pointer(5, 50, &sar);
  int a = read_scalar_by_pointer(&sar);
  int b = read_aggreg_by_pointer(5, &sar);
  printf("a = %d\nb = %d\n", a, b);
}

void test_flex_struct_read_write() {
  struct flex *p = (struct flex *) malloc(sizeof(struct flex) + 10);
  write_flex_last(p, 5, 11);
  unsigned char c = read_flex_last(p, 5);
  printf("c = %d\n", c);
}

int main(void) {
  test_read_from_point2D_by_value();
  test_read_from_point2D_by_pointer();
  test_write_to_point2D_by_value();
  test_write_to_point2D_by_pointer();
  test_allpos_by_value();
  test_allpos_by_pointer();
  test_read_from_scalar_and_array();
  test_write_to_scalar_and_array_by_value();
  test_write_to_scalar_and_array_by_pointer();
  test_flex_struct_read_write();
  return 0;
}
