struct point {
  int x;
  int z;
};

static struct point p;

void setz(struct point *q, int v);

void setz(struct point *q, int v) {
  q->z = v;
}

int getx(struct point pt) {
  return pt.x;
}

int main(void) {
  setz(&p, 5);
  return getx(p);
}
