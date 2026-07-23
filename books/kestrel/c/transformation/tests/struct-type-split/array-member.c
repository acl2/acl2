struct point {
  int x;
  int z;
};

struct outer {
  struct point arr[2];
  int w;
};

static struct outer o = {
  .arr = { [0] = { .x = 1, .z = 2 }, [1] = { .x = 3, .z = 4 } },
  .w = 9
};

int main(void) {
  return o.arr[0].x + o.arr[1].z;
}
