// RAC begin

enum Num { ONE = 1, TWO = 2 }; 

int foo(int a)
{
  int b = 0;

  switch (a)
  {
    case ONE: b = 1; break;
    case TWO: b = 2; break;
    default: b = 3;
  }
  
  return b;
}


// RAC end
