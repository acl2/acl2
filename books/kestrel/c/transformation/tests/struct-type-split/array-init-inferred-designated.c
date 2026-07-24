struct point {
  int x;
  int z;
};

static struct point arr[] = {
  [5].x = 1,
  [2].z = 2,
};

int main(void) {
  return arr[5].x + arr[2].z + arr[5].z;
}
