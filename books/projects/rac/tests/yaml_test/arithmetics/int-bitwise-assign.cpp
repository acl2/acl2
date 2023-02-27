// RAC begin

int foo(int a)
{
  a >>= 1;
  a <<= 1;
  a &= 1;
  a |= 1;
  a ^= 1;

  return a;
}

// RAC end
