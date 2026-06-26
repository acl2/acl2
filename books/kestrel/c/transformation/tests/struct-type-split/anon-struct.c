struct point {
  int x;
  int z;
};

struct outer {
  struct {
    struct point inner;
  };
  int w;
};

static struct outer o;

int main(void) {
  return o.inner.x;
}
