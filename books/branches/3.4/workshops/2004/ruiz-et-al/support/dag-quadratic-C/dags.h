/// C implementation of the Q-dag-unification algorithm
/// Author: ChesKo (fjesus@us.es)
///****************************************************************************

#include <stdio.h>
#include "lists.h"
#include "terms.h"

///****************************************************************************
/// DAG
///****************************************************************************

typedef struct dagcell {
  int stamp;
  int dagcelltype;    // 0 - direction, 1 - variable, 2 - function
  int direction;
  char symbol[5];
  Intlist *args;
} DagCell;

///****************************************************************************
/// Print function
///****************************************************************************

void print_dag (DagCell *, int);

///****************************************************************************
/// Terms to DAG representation
///****************************************************************************

int term_as_dag_st_aux (Term *, DagCell *, int, Varlist **);

///****************************************************************************
