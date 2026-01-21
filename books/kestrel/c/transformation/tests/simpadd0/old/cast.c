int cast_long_to_int(long x) {
  return (int) x;
}

long cast_int_to_long(int x) {
  return (long) x;
}

short cast_nonpure(int x) {
  return (short) (x = 5 + 0);
}
