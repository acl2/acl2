struct point {
  int x;
  int z;
};

struct holder {
  struct point grid[2][3];
};

static struct holder h = {
  .grid = {
    [0][1] = { .x = 1, .z = 2 },
    [1][2].x = 3,
    [1][2].z = 4
  }
};

static struct point inferred[] = {
  [5].z = 6,
  [2].x = 5
};

static int sum(struct point a[2]) {
  return a[0].x + a[1].z;
}

int main(void) {
  return h.grid[0][1].x
    + h.grid[1][2].z
    + inferred[2].x
    + inferred[5].z
    + sum((struct point[2]) {
        [0] = { .x = 7, .z = 8 },
        [1] = { .x = 9, .z = 10 }
      });
}
