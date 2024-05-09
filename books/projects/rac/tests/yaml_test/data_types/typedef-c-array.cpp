// RAC begin

typedef int fixed_size_arr[4];

int foo()
{
  fixed_size_arr a;
  a[2] = 3;
  return a[2];
}

// RAC end
