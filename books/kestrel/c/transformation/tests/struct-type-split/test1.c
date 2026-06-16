struct point {
  int x;
  int y;
  int z;
};

static struct point p;

int main(void) {
  p.x = 4;
  p.z = 2;
  return p.x + p.z;
}
