struct point {
  int x;
  int z;
};

static struct point arr[2];

int main(void) {
  return arr[0].x;
}
