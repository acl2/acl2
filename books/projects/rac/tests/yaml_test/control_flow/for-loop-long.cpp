typedef long int64;
typedef unsigned long uint64;

// RAC begin

int foo() {
  int res = 0;
  for (int64 i = 0; i < 5; i += 1)
    res += i;
  return res;
}

int bar() {
  int res = 0;
  for (uint64 i = 0; i < 5; i += 1)
    res += i;
  return res;
}

// RAC end
