struct point {
  int x;
  int z;
};

struct outer {
  struct {
    struct point inner;
  };
  int inner_0;
};

static struct outer o;

int main(void) {
  return o.inner.x + o.inner.z + o.inner_0;
}
