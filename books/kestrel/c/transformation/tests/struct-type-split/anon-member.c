struct point {
  int x;
  int : 8;
  int z;
};

static struct point p;

int main(void) {
  return p.x;
}
