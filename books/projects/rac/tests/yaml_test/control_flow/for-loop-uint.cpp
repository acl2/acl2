typedef unsigned uint;

// RAC begin

int foo() {
  int res = 0;
  for (uint i = 0; i < 5; i += 1)
    res += i;
  return res;
}

// RAC end
