struct point {
  int x;
  int z;
  struct point *next;
};

static struct point p;

int main(void) {
  return p.x;
}
