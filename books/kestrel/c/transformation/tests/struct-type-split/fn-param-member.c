struct point {
  int x;
  int z;
};

typedef struct {
  struct point inner;
  int w;
} container;

int get(container *c) {
  return c->inner.x + c->inner.z;
}

int main(void) {
  container c;
  return get(&c);
}
