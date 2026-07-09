struct point {
  int x;
  int z;
};

struct outer {
  struct point inner;
  int w;
};

static struct outer braced = { { 1, 2 }, 9 };
static struct outer flat = { 1, 2, 9 };
static struct outer desig = { .inner = { 1, 2 }, .w = 9 };

int main(void) {
  return braced.inner.x + flat.w + desig.inner.z;
}
