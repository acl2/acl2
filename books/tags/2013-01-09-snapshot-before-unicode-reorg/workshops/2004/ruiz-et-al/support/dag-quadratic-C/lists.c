/// Ordered lists
/// Author: ChesKo
///****************************************************************************

#include "lists.h"

///****************************************************************************
/// Ordered lists
///****************************************************************************

Varlist *varlistalloc(void) {
  return (Varlist *) malloc(sizeof(struct varlist));
}

Varlist *varlistadd(Varlist *vl, char newsymbol[5], int newdirection) {
  Varlist *newvl;
  Varlist *res;
  res = varlistalloc();

  if ( vl == NULL || strcmp(newsymbol,vl->symbol) < 0 ) {
    newvl = varlistalloc();
    strcpy(newvl->symbol,newsymbol);
    newvl->direction = newdirection;
    newvl->rest = vl;
    res->direction = newdirection;
    res->rest = newvl;
  } else if ( strcmp(newsymbol,vl->symbol) == 0 ) {
    res->direction = vl->direction;
    res->rest = vl;
  } else {
    res->rest = vl;
    while ( vl->rest != NULL && strcmp(newsymbol,vl->rest->symbol) > 0 ) {
      vl = vl->rest;
    }
    if ( vl->rest == NULL || strcmp(newsymbol,vl->rest->symbol) < 0 ) {
      newvl = varlistalloc();
      strcpy(newvl->symbol,newsymbol);
      newvl->direction = newdirection;
      newvl->rest = vl->rest;
      vl->rest = newvl;
      res->direction = newdirection;
    } else {
      res->direction = vl->rest->direction;
    }
  }
  return res;
} 

///****************************************************************************

/// Print function

void print_varlist ( Varlist *vl ) {
  if ( vl == NULL ) {
    printf(".\n");
  } else {
    if ( vl->rest == NULL ) {
      printf("(%s,%d).\n", vl->symbol, vl->direction);
    } else {
      while ( vl->rest != NULL ) {
	printf("(%s,%d) -> ", vl->symbol, vl->direction);
	vl = vl->rest;
      }
      printf("(%s,%d).\n", vl->symbol, vl->direction);
    }
  }
}

///****************************************************************************
/// Integer lists
///****************************************************************************

Intlist *intlistalloc(void) {
  return (Intlist *) malloc(sizeof(struct intlist));
}

Intlist *intlistadd( Intlist *il , int i ) {
  Intlist *newil;
  newil = intlistalloc();
  newil->val = i;
  newil->rest = NULL;
  if ( il == NULL ) {
    return newil;
  } else {
    Intlist *orig = il;
    while ( il->rest != NULL ) 
      il = il->rest;
    il->rest = newil;
    return orig;
  }
}

int intlistlength( Intlist *il ) {
  int res;
  res = 0;
  while ( il != NULL ) {
    il = il->rest;
    res++;
  }
  return res;
}

///****************************************************************************

/// Print function

void print_intlist ( Intlist *il ) {
  if ( il == NULL ) {
    printf(".\n");
  } else {
    if ( il->rest == NULL ) {
      printf("%d.\n", il->val);
    } else {
      while ( il->rest != NULL ) {
	printf("%d -> ", il->val);
	il = il->rest;
      }
      printf("%d.\n", il->val);
    }
  }
}

///****************************************************************************
