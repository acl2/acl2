struct point {
  int x;
  int z;
  void (*setz)(struct point *p);
};

void setz(struct point *p) {
  p->z = 2;
}

int main(void) {
  struct point p;
  p.setz = setz;
  p.setz(&p);
  return p.z;
}
