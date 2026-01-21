int ternary_pure(int x, int y, int z) {
  return x ? y : z;
}

int ternary_nonpure(int x, int y, int z, int w) {
  return (x = w + 0) ? (x = ~w) : (x = !w);
}
