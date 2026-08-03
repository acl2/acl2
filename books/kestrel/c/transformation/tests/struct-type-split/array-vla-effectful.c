struct point {
  int x;
  int z;
};

void f(int n) {
  struct point arr[n++];
  arr[0].z = 0;
}
