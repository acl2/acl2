// RAC begin

template <int i, int j>
int foo()
{
  return i + j;
}

template <int i, int j>
int foo2()
{
  return i + j;
}

int bar()
{
  return foo<2, 4>() + foo2<1, 3>();
}

// RAC end
