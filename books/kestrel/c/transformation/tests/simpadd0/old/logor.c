int logor(short x, long y) {
  return x || y;
}

int logor_nonpure(int x, int y, int z) {
  return (x = !z + 0) || (y = z);
}
