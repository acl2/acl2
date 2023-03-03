typedef unsigned uint;

// RAC begin

int bit_and(int a, int b)
{
  return a & b;
}

int bit_or(int a, int b)
{
  return a | b;
}

int bit_not(int a)
{
  return ~a;
}

int shift_left(int a, uint n)
{
  return a << n;
}

int shift_right(int a, uint n)
{
  return a >> n;
}

int bit_xor(int a, int b)
{
  return a ^ b;
}

// RAC end
