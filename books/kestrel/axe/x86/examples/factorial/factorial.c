// A simple factorial program
//
// Copyright (C) 2017-2021 Kestrel Technology, LLC
// Copyright (C) 2023 Kestrel Institute
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Eric Smith (eric.smith@kestrel.edu)

////////////////////////////////////////////////////////////////////////////////

#include <stdio.h>
#include <stdlib.h>

int fact(int x) {
  int res = 1;
  int i;
  for(i = x; i > 0; i--) {
    res = res * i;
  }
  return res;
}

int main (int argc, char *argv[], char *env[])
{
  int x;
  printf ("\nEnter the value x: ");
  scanf  ("%d", &x);
  printf ("\nFact %d is: %d\n", x, fact(x));
  return 0;
}
