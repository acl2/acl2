/// C implementation of well formed terms
/// Author: ChesKo (fjesus@us.es)
///****************************************************************************

#include <stdio.h>

///****************************************************************************
/// Terms
///****************************************************************************

typedef struct termlist {
    struct term *first;
    struct termlist *rest;
} Termlist;

typedef struct term {
    char symbol[5];
    struct termlist *args;
} Term;

///****************************************************************************
/// Constructor functions
///****************************************************************************

Term *termalloc(void);
Termlist *termlistalloc(void);
Term *make_var (int);
Term *make_const (char *);
Term *make_fun (char *, Termlist *);

///****************************************************************************
/// Length function
///****************************************************************************

int length_term (Term *);

///****************************************************************************
/// Print functions
///****************************************************************************

void print_term(Term *);
void print_termlist(Termlist *);
void print_initterm(Term *);

///****************************************************************************
/// Exponential examples
///****************************************************************************

Term *exp_unif_problem_t1 (int);
Term *exp_unif_problem_t2 (int);

Term *exp_unif_problem_t1_rev (int);
Term *exp_unif_problem_t2_rev (int);

Term *exp_unif_problem_t1_q (int);
Term *exp_unif_problem_t2_q (int);

Term *exp_unif_problem_t1_qn (int);
Term *exp_unif_problem_t2_qn (int);

///****************************************************************************
