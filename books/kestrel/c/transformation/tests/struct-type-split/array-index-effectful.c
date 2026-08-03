struct point {
  int x;
  int z;
};

static struct point arr[2];

int main(void) {
  int i = 0;
  return arr[i++].z;
}
