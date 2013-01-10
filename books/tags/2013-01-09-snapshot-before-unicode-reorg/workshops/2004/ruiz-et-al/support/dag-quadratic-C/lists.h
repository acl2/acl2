/// Ordered lists
/// Author: ChesKo
///****************************************************************************

#include <stdio.h>

///****************************************************************************
/// Ordered lists
///****************************************************************************

typedef struct varlist {
  char symbol[5];
  int direction;
  struct varlist *rest;
} Varlist;

Varlist *varlistadd(Varlist *, char [5], int);

///****************************************************************************
/// Integer lists
///****************************************************************************

typedef struct intlist {
    int val;
    struct intlist *rest;
} Intlist;

Intlist *intlistadd(Intlist *, int);
int intlistlength(Intlist *);
void print_intlist(Intlist *);

///****************************************************************************
