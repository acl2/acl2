struct point {
  int x;
  int z;
};

struct outer {
  struct point inner;
};

static struct outer o;

int main(void) {
  return o.inner.x;
}
