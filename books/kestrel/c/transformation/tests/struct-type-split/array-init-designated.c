struct point {
  int x;
  int z;
};

static struct point arr[2] = {
  [0] = { .x = 1, .z = 2 },
  [1].z = 4,
  [1].x = 3
};

int main(void) {
  return arr[0].x + arr[1].z;
}
