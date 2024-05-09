#include <cstdint>
// RAC had a type `uint` but there is no such type in C++.
typedef unsigned uint;
typedef int64_t int64;
typedef uint64_t uint64;


// RAC begin

int64 int64_func(int64 a)
{
  return a;
}

uint64 uint64_func(uint64 a)
{
  return a;
}

int int_func(int a)
{
  return a;
}

uint uint_func(int b)
{
  return b;
}

bool bool_func(int c)
{
  return c;
}

// RAC end
