struct point {
  int x;
  int z;
};

static struct point arr[2];

static int get(struct point *p) {
  return p->x + p->z;
}

int main(void) {
  arr[1].z = arr[0].x;
  return get(&arr[1]);
}
