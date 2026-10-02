struct point {
  int x;
  int z;
};

static struct point matrix[2][3];
static struct point *ptrs[2];

static int first(struct point (*)[3]);
static int sum(int, struct point [*][3]);

static int sum(int n, struct point a[n][3]) {
  return a[1][2].x + a[1][2].z;
}

static int first(struct point (*p)[3]) {
  return (*p)[0].x + (*p)[0].z;
}

static int use_vla(int n) {
  struct point vla[n][2];
  vla[0][1].x = 1;
  vla[0][1].z = 2;
  return vla[0][1].x + vla[0][1].z;
}

int main(void) {
  ptrs[0] = &matrix[0][0];
  return sum(2, matrix) + first(matrix) + ptrs[0]->x + use_vla(2);
}
