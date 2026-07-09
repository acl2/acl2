struct point {
  int x;
  int z;
};

struct outer {
  struct point inner;
  int w;
};

struct wrapper {
  struct outer out;
  int tag;
};

static struct wrapper w = { { { 1, 2 }, 9 }, 7 };

int main(void) {
  return w.out.inner.x + w.out.inner.z;
}
