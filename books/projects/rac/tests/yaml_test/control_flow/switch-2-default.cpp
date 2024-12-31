// RAC begin

int foo(int a) {
  int b = 0;

  switch (a) {
  default:
    b = 1;
    break;
  default:
    b = 2;
    break;
  }

  return b;
}

// RAC end
