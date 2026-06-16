struct point {
  int x;
  int z;
};

struct point *get(void);

static struct point p;

int main(void) {
  return p.x;
}
