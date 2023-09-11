#include <stdio.h>
#include <stdlib.h>

int add(int x, int y)
{
  return(x+y);
}

int main (int argc, char *argv[], char *env[])
{
  int x;
  printf ("\nEnter the value x: ");
  scanf  ("%d", &x);
  int y;
  printf ("\nEnter the value y: ");
  scanf  ("%d", &y);
  printf ("\nSum of %d and %d is: %d\n", x, y, add(x,y));
  return 0;
}
