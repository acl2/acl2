struct point {
  int x;
  int z;
};

typedef struct {
  struct point inner;
  int w;
} container;

static container c = { { 1, 2 }, 9 };

int main(void) {
  return c.inner.x + c.inner.z;
}
