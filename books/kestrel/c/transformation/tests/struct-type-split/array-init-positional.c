struct point {
  int x;
  int z;
};

static struct point arr[2] = { { 1, 2 }, { 3, 4 } };

int main(void) {
  return arr[0].x + arr[1].z;
}
