// RAC begin

struct S
{
  enum { a = 1 } x;
};


int foo()
{
  S s;
  return s.x;
}


// RAC end
