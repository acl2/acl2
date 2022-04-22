#include <stdio.h>

struct point2D { // copied from structs.c
    int x;
    int y;
};

void test_read_from_point2D() {
  struct point2D point = {.x = 11, .y = 22};
  int x = read_x_from_point2D(&point);
  int y = read_y_from_point2D(&point);
  printf("point = (%d, %d)\n", x, y);
}

void test_write_to_point2D() {
  struct point2D point = {.x = 11, .y = 22};
  write_x_to_point2D(&point);
  write_y_to_point2D(&point);
  printf("point = (%d, %d)\n", point.x, point.y);
}

int main(void) {
  test_read_from_point2D();
  test_write_to_point2D();
  return 0;
}
