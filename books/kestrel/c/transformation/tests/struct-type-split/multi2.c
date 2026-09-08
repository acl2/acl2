struct point {
  int x;
  int y;
  int z;
};

extern struct point p;

int getz(void) {
  return p.z;
}
