struct point {
  int x;
  int z;
};

struct outer {
  union {
    struct point p;
    int tag;
  };
  int w;
};

static struct outer o;

int main(void) {
  return o.p.x;
}
