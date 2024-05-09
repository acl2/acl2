// RAC begin

int foo(int a)
{
  int b = 0;

  switch (a)
  {
    case 1: b = 1;
    case 2: b = 2; break;
    default: b = 3;
  }
  
  return b;
}


// RAC end
