struct point {
  int x;
  int z;
};

typedef struct {
  struct point inner;
  int w;
} container;

static container c;
static container *p = &c;

int main(void) {
  return p->inner.x + p->inner.z;
}
