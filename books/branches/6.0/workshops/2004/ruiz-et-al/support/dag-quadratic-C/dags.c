/// C implementation of the Q-dag-unification algorithm
/// Author: ChesKo (fjesus@us.es)
///****************************************************************************

#include <time.h>
#include "dags.h"

#define BOOLEAN int
#define FALSE   0
#define TRUE    1

///****************************************************************************
/// Print function
///****************************************************************************

void print_dag (DagCell *terms_dag, int len) {
  int h;
  for ( h = 0; h< len; h++) {
    switch ( terms_dag[h].dagcelltype ) {
	case 0:
	  printf("| %d |%d -> %d\n", h, terms_dag[h].stamp, 
		 terms_dag[h].direction);
	  break;
	case 1:
	  printf("| %d |%d : %s\n", h, terms_dag[h].stamp, 
		 terms_dag[h].symbol);
	  break;
	case 2:
	  printf("| %d |%d : %s -> ", h, terms_dag[h].stamp, 
		 terms_dag[h].symbol);
	  print_intlist( terms_dag[h].args );
	  break;
	default: 
	  printf("| %d |\n", h);
    }
  }
}

///****************************************************************************
/// Terms to DAG representation
///****************************************************************************

int term_as_dag_st_aux (Term *t, DagCell *terms_dag, int h, Varlist **vl) {
  terms_dag[h].stamp = 0;
  if ( t->args == NULL ) {
    *vl = varlistadd(*vl,t->symbol,h);
    int direction = (*vl)->direction;
    *vl = (*vl)->rest;
    if ( direction != h ) {
      terms_dag[h].dagcelltype = 0;
      terms_dag[h].direction = direction;
      return h+1;
    } else {
      terms_dag[h].dagcelltype = 1;
      strcpy(terms_dag[h].symbol,t->symbol);
      return h+1;
    }
  } else {
    Termlist *args;
    args = t->args;
    terms_dag[h].dagcelltype = 2;
    strcpy(terms_dag[h].symbol,t->symbol);
    int newh = h+1;
    terms_dag[h].args = NULL;

    if ( args->first != NULL )
      while ( args != NULL ) {
	terms_dag[h].args = intlistadd(terms_dag[h].args,newh);
	newh = term_as_dag_st_aux(args->first, terms_dag, newh, vl);
	args = args->rest;
      }
    return newh;
  }
}

///****************************************************************************
/// Occur check
///****************************************************************************

BOOLEAN occur_check (char *symbol, int h, DagCell *terms_dag, int time) {
  while ( terms_dag[h].dagcelltype == 0 )
    h = terms_dag[h].direction;
  switch ( terms_dag[h].dagcelltype ) {
      case 1:
	return ( strcmp(symbol,terms_dag[h].symbol) == 0 );
	break;
      case 2:
	if ( terms_dag[h].stamp == time )
	  return FALSE;
	else {
	  Intlist *args;
	  args = terms_dag[h].args;
	  BOOLEAN occur = FALSE;
	  while ( args != NULL && !occur ) {
	    occur = occur_check ( symbol, args->val, terms_dag, time );
	    args = args->rest;
	  }
	  if ( !occur )
	    terms_dag[h].stamp = time;
	  return occur;
	}
  }
}

///****************************************************************************
/// Unification procedure
///****************************************************************************

BOOLEAN unification_dag ( int h1, int h2, DagCell *terms_dag, int *time) {
  while ( terms_dag[h1].dagcelltype == 0 )
    h1 = terms_dag[h1].direction;
  while ( terms_dag[h2].dagcelltype == 0 )
    h2 = terms_dag[h2].direction;
  if ( h1 == h2 ) {
    return TRUE;
  } else if ( terms_dag[h1].dagcelltype == 1 ) {
    if ( occur_check(terms_dag[h1].symbol, h2, terms_dag, *time) == 1 )
      return FALSE;
    else {
      terms_dag[h1].dagcelltype = 0;
      terms_dag[h1].direction = h2;
      *time = *time+1;
      return TRUE;
    }
  } else if ( terms_dag[h2].dagcelltype == 1 ) {
    if ( occur_check(terms_dag[h2].symbol, h1, terms_dag, *time) == 1 )
      return FALSE;
    else {
      terms_dag[h2].dagcelltype = 0;
      terms_dag[h2].direction = h1;
      *time = *time+1;
      return TRUE;
    }
  } else if ( strcmp(terms_dag[h1].symbol,terms_dag[h2].symbol) != 0 ) {
    return FALSE;
  } else if ( intlistlength(terms_dag[h1].args) != 
	      intlistlength(terms_dag[h2].args) ) {
    return FALSE;
  } else {
    Intlist *args1;
    Intlist *args2;
    args1 = terms_dag[h1].args;
    args2 = terms_dag[h2].args;
    BOOLEAN unif = TRUE;
    while ( args1 != NULL && unif ) {
      unif = unification_dag( args1->val, args2->val, terms_dag, time );
      args1 = args1->rest;
      args2 = args2->rest;
    }
    if ( unif ) {
      terms_dag[h1].dagcelltype = 0;
      terms_dag[h1].direction = h2;
    }
    return unif;
  }
}    

///****************************************************************************
/// Unification procedure with terms as arguments
///****************************************************************************

BOOLEAN unification_terms ( Term *t1, Term *t2 ) {
  Termlist *args;
  Termlist *this;

  args = NULL;
  this = termlistalloc();
  this->first = t1;
  this->rest = args;
  args = this;
  this = termlistalloc();
  this->first = t2;
  this->rest = args;
  args = this;

  Term *eq;
  Varlist *vl;
  int l;
  int time;

  vl = NULL;
  eq = make_fun("eq",args);
  l = length_term(eq);
  DagCell terms_dag[l];

  term_as_dag_st_aux(eq, terms_dag, 0, &vl);

  time = 1;
  return unification_dag(terms_dag[0].args->val, terms_dag[0].args->rest->val,
			 terms_dag, &time);

}  
  
///****************************************************************************

/// Tests

/// problem = 0 -> exp_unif_problem
/// problem = 1 -> exp_unif_problem_rev
/// problem = 2 -> exp_unif_problem_q
/// problem = 3 -> exp_unif_problem_qn

void test_exp_unif (int problem, int number, int inc, int rep) {
  clock_t start, end;
  double cpu_time_used, total_time_used;

  int i, j, n;
  switch ( problem ) {
    case 0:
      printf("exp_unif_problem\n");
      printf("----------------\n");
      break;
    case 1:
      printf("exp_unif_problem_rev\n");
      printf("--------------------\n");
      break;
    case 2:
      printf("exp_unif_problem_q\n");
      printf("------------------\n");
      break;
    case 3:
      printf("exp_unif_problem_qn\n");
      printf("-------------------\n");
      break;
  }
  for ( j = 0 ; j < rep+2 ; j++ ) printf("+=========");
  printf("+\n");
  printf("| Formula | Time    ");
  for ( j = 1 ; j < rep ; j++ ) printf("          ");
  printf("| Mean    |\n");
  for ( j = 0 ; j < rep+2 ; j++ ) printf("+---------");
  printf("+\n");
  for ( i = 1 ; i <= number ; i++ ) {
    n = inc*i;
    total_time_used = 0;
    printf("|  %5d  |", n);
    for ( j = 0 ; j < rep ; j++ ) {
      switch ( problem ) {
	case 0:  
	  start = clock();
	  unification_terms(exp_unif_problem_t1(n), exp_unif_problem_t2(n));
	  end = clock();
	  break;
	case 1:  
	  start = clock();
	  unification_terms(exp_unif_problem_t1_rev(n), exp_unif_problem_t2_rev(n));
	  end = clock();
	  break;
	case 2:  
	  start = clock();
	  unification_terms(exp_unif_problem_t1_q(n), exp_unif_problem_t2_q(n));
	  end = clock();
	  break;
	case 3:  
	  start = clock();
	  unification_terms(exp_unif_problem_t1_qn(n), exp_unif_problem_t2_qn(n));
	  end = clock();
	  break;
      }
      cpu_time_used = ((double) (end - start)) / CLOCKS_PER_SEC;
      total_time_used += cpu_time_used;
      printf("%8.3f |", cpu_time_used);
    }
    printf("%8.3f |\n", total_time_used / rep);
  }
  for ( j = 0 ; j < rep+2 ; j++ ) printf("+---------");
  printf("+\n\n");
}

main (int argc, char *argv[]) {
  int problem = atoi(argv[1]);
  int number = atoi(argv[2]);
  int inc = atoi(argv[3]);
  int rep = atoi(argv[4]);  
  test_exp_unif(problem,number,inc,rep);
  return 0;
}

///****************************************************************************
