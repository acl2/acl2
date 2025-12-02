int logand(short x, long y) {
  return x && y;
}

int logand_nonpure(int x, int y, int z) {
  return (x = z) && (y = ~z);
}
