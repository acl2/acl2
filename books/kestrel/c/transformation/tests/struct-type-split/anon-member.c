struct point {
  int x;
  int b : 4;
  union { int c; int d; };
  int : 8;
  int z;
};

static struct point p;

int main(void) {
  p.c = 3;
  return p.x + p.b + p.z;
}
