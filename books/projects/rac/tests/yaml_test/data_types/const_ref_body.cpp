// RAC begin

int foo(int a) {
  const int& b = a;
  return b;
}

// RAC end
