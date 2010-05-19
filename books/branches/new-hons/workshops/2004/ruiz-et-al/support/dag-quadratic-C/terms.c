/// C implementation of well formed terms
/// Author: ChesKo (fjesus@us.es)
///****************************************************************************

#include "terms.h"

///****************************************************************************
/// Constructor functions
///****************************************************************************

Term *termalloc(void) {
  return (Term *) malloc(sizeof(struct term));
}

Termlist *termlistalloc(void) {
  return (Termlist *) malloc(sizeof(struct termlist));
}

Term *make_var (int i) {
  Term *t;
  char symbol[5];

  t = termalloc();
  sprintf(symbol,"%d",i);
  strcpy(t->symbol,symbol);
  t->args = NULL;
  return t;
}

Term *make_const (char *symbol) {
  Term *t;
  Termlist *args;
  t = termalloc();
  strcpy(t->symbol,symbol);
  args = termlistalloc();
  args->first = NULL;
  args->rest = NULL;
  t->args = args;
  return t;
}

Term *make_fun (char *symbol, Termlist *args) {
  Term *t;
  t = termalloc();
  strcpy(t->symbol,symbol);
  t->args = args;
  return t;
}

///****************************************************************************
/// Print functions
///****************************************************************************

void print_termlist (Termlist *ts) {
  if ( ts != NULL ) {
    print_term (ts->first);
    if ( ts->rest != NULL ) {
      printf(",");
      print_termlist (ts->rest);
    }
  }
}

void print_term (Term *t) {
  if ( t->args == NULL ) {
    printf("%s",t->symbol);
  } else if ( t->args->first == NULL ) {
    printf("%s()",t->symbol);
  } else {
    printf("%s(",t->symbol);
    print_termlist (t->args);
    printf(")");
  }
}

void print_initterm (Term *t) {
  print_term(t);
  printf("\n");
}

///****************************************************************************
/// Length function
///****************************************************************************

int length_term (Term *t) {
  if ( t->args == NULL ) {
    return 1;
  } else if ( t->args->first == NULL ) {
    return 1;
  } else {
    int res = 1;
    Termlist *args;
    args = t->args;
    while ( args != NULL ) {
      res += length_term(args->first);
      args = args->rest;
    }
    return res;
  }
}

///****************************************************************************
/// Exponential problems
///****************************************************************************

///   See pages 85 and 86 of {\em Term Rewriting and All That...}, Baader \&
/// Nipkow. We now define functions building unification problems for solving
/// the equations $\{x_n=f(x_{n-1},x_{n-1}),\ldots,x_1=f(x_0,x_0)\}$

///   Auxiliary functions to build the unification problem:

Termlist *list_of_n (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  for ( i = 1; i <= n; i++ ) {
    this = termlistalloc();
    this->first = make_var(i);
    this->rest = args;
    args = this;
  }
  return args;
}

Term *make_fun_args(char* symbol, int n, int m) {
  Term *t;
  Termlist *args;
  Termlist *this;

  args = NULL;
  this = termlistalloc();
  this->first = make_var(m);
  this->rest = args;
  args = this;
  this = termlistalloc();
  this->first = make_var(n);
  this->rest = args;
  args = this;

  t = termalloc();
  strcpy(t->symbol,symbol);
  t->args = args;
  return t;
}

Termlist *list_of_f (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  for ( i = 0; i < n; i++ ) {
    this = termlistalloc();
    this->first = make_fun_args("f",i,i);
    this->rest = args;
    args = this;
  }
  return args;
}

Term *exp_unif_problem_t1 (int n) {
  return make_fun("l",list_of_n(n));
}

Term *exp_unif_problem_t2 (int n) {
  return make_fun("l",list_of_f(n));
}

///----------------------------------------------------------------------------

///   If we change the order in which the equations are selected, the
/// exponential algorithm defined in {\tt dag-unification-st-program.lisp}
/// needs a lot of time. It is not the case now:

Termlist *revlist_of_n (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  for ( i = n; i > 0; i-- ) {
    this = termlistalloc();
    this->first = make_var(i);
    this->rest = args;
    args = this;
  }
  return args;
}

Termlist *revlist_of_f (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  for ( i = n-1; i >= 0; i-- ) {
    this = termlistalloc();
    this->first = make_fun_args("f",i,i);
    this->rest = args;
    args = this;
  }
  return args;
}

Term *exp_unif_problem_t1_rev (int n) {
  return make_fun("l",revlist_of_n(n));
}

Term *exp_unif_problem_t2_rev (int n) {
  return make_fun("l",revlist_of_f(n));
}

///----------------------------------------------------------------------------

Termlist *list_of_n_q (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  this = termlistalloc();
  this->first = make_var(n);
  this->rest = args;
  args = this;
  for ( i = 1; i <= n; i++ ) {
    this = termlistalloc();
    this->first = make_var(-i);
    this->rest = args;
    args = this;
  }
  for ( i = 1; i <= n; i++ ) {
    this = termlistalloc();
    this->first = make_var(i);
    this->rest = args;
    args = this;
  }
  return args;
}

Termlist *list_of_f_q (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  this = termlistalloc();
  this->first = make_var(-n);
  this->rest = args;
  args = this;
  for ( i = 0; i < n; i++ ) {
    this = termlistalloc();
    this->first = make_fun_args("f",-i,-i);
    this->rest = args;
    args = this;
  }
  for ( i = 0; i < n; i++ ) {
    this = termlistalloc();
    this->first = make_fun_args("f",i,i);
    this->rest = args;
    args = this;
  }
  return args;
}

Term *exp_unif_problem_t1_q (int n) {
  return make_fun("l",list_of_n_q(n));
}

Term *exp_unif_problem_t2_q (int n) {
  return make_fun("l",list_of_f_q(n));
}

///----------------------------------------------------------------------------

Termlist *list_of_n_qn (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  this = termlistalloc();
  this->first = make_const("a");
  this->rest = args;
  args = this;
  this = termlistalloc();
  this->first = make_var(n);
  this->rest = args;
  args = this;
  for ( i = 1; i <= n; i++ ) {
    this = termlistalloc();
    this->first = make_var(-i);
    this->rest = args;
    args = this;
  }
  for ( i = 1; i <= n; i++ ) {
    this = termlistalloc();
    this->first = make_var(i);
    this->rest = args;
    args = this;
  }
  return args;
}

Termlist *list_of_f_qn (int n) {
  int i;
  Termlist *args;
  Termlist *this;

  args = NULL;
  this = termlistalloc();
  this->first = make_const("b");
  this->rest = args;
  args = this;
  this = termlistalloc();
  this->first = make_var(-n);
  this->rest = args;
  args = this;
  for ( i = 0; i < n; i++ ) {
    this = termlistalloc();
    this->first = make_fun_args("f",-i,-i);
    this->rest = args;
    args = this;
  }
  for ( i = 0; i < n; i++ ) {
    this = termlistalloc();
    this->first = make_fun_args("f",i,i);
    this->rest = args;
    args = this;
  }
  return args;
}

Term *exp_unif_problem_t1_qn (int n) {
  return make_fun("l",list_of_n_qn(n));
}

Term *exp_unif_problem_t2_qn (int n) {
  return make_fun("l",list_of_f_qn(n));
}

///****************************************************************************
