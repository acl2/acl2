/************************************************************************************[drat-trim.c]
Copyright (c) 2014-2015, Marijn Heule and Nathan Wetzler
Last edit, March 4, 2015

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <sys/time.h>

#define TIMEOUT     20000
#define BIGINIT     1000000
#define INIT        8
#define END         0
#define UNSAT       0
#define SAT         1
#define EXTRA       3
#define INFOBITS    2
#define ASSUMED     2
#define MARK        3
#define ERROR      -1
#define ACTIVE      1
#define ID         -1
#define PIVOT      -2
//#define DEPTH      -3

#define FORWARD_SAT      10
#define FORWARD_UNSAT    20
#define BACKWARD_UNSAT   30
#define SUCCEED          40
#define FAILED           50

#define CANDIDATE_INIT_SIZE    10
#define DEPENDENCIES_INIT_SIZE 10

struct solver { FILE *inputFile, *proofFile, *coreFile, *lemmaFile, *traceFile;
    int *DB, nVars, timeout, mask, delete, *falseStack, *false, *forced,
      *processed, *assigned, count, *used, *max, *delinfo, COREcount, RATmode, RATcount, MARKcount,
      Lcount, maxCandidates, *resolutionCandidates, maxDependencies, nDependencies,
      *dependencies, maxVar, mode, verb, unitSize, prep, *current, delLit; // depth, maxdepth;
    struct timeval start_time;
    long mem_used, time, nClauses, lastLemma, *unitStack, *reason, lemmas, arcs, *adlist, **wlist;  };

#define ASSUME(a)	{ S->false[-(a)] = ASSUMED; *(S->assigned++) = -(a); S->reason[abs(a)] = 0; }
#define ASSIGN(a)	{ S->false[-(a)] = 1; *(S->assigned++) = -(a); }
#define ADD_WATCH(l,m)  { if (S->used[(l)] + 1 == S->max[(l)]) { S->max[(l)] *= 1.5; \
                            S->wlist[(l)] = (long *) realloc(S->wlist[(l)], sizeof(long) * S->max[(l)]); } \
                          S->wlist[(l)][ S->used[(l)]++ ] = (m); S->wlist[(l)][ S->used[(l)] ] = END; }

static inline void printClause(int* clause) {
  printf("[%i] ", clause[ID]);
  while(*clause) printf("%i ", *clause++); printf("0\n"); }

static inline void addWatch (struct solver* S, int* clause, int index) {
  int lit = clause[ index ];
  if (S->used[lit] + 1 == S->max[lit]) { S->max[lit] *= 1.5;
    S->wlist[lit] = (long*) realloc(S->wlist[lit], sizeof(long) * S->max[lit]); }
  S->wlist[lit][ S->used[lit]++ ] = ((long) (((clause) - S->DB)) << 1) + S->mask;
  S->wlist[lit][ S->used[lit]   ] = END; }

static inline void removeWatch (struct solver* S, int* clause, int index) {
  int lit = clause[index]; long *watch = S->wlist[lit];
  for (;;) {
    int* _clause = S->DB + (*(watch++) >> 1);
    if (_clause == clause) {
      watch[-1] = S->wlist[lit][ --S->used[lit] ];
      S->wlist[lit][ S->used[lit] ] = END; return; } } }

static inline void addUnit (struct solver* S, long index) {
  S->unitStack[ S->unitSize++ ] = index; }

static inline void removeUnit (struct solver* S, int lit) {
  int i, found = 0;
  for (i = 0; i < S->unitSize; i++) {
    if (found) S->unitStack[i - 1] = S->unitStack[i];
    if (S->DB[ S->unitStack[i] ] == lit) found = 1; }
  S->unitSize--; }

static inline void unassignUnit (struct solver* S, int lit) {
  if (S->verb)
    printf("c removing unit %i\n", lit);
  while (S->false[-lit]) {
    if (S->verb)
      printf("c removing unit %i (%i)\n", S->forced[-1], lit);
    S->false[*(--S->forced)] = 0; }
  S->processed = S->assigned = S->forced; }

static inline void markWatch (struct solver* S, int* clause, int index, int offset) {
  long* watch = S->wlist[ clause[ index ] ];
  for (;;) {
    int *_clause = (S->DB + (*(watch++) >> 1) + (long) offset);
    if (_clause == clause) { watch[-1] |= ACTIVE; return; } } }

static inline void markClause (struct solver* S, int* clause, int index) {
  S->arcs++;
//  if (clause[DEPTH+index] <= S->depth) clause[DEPTH+index] = S->depth + 1;
  if (S->traceFile) {
    if (S->nDependencies == S->maxDependencies) {
      S->maxDependencies = (S->maxDependencies * 3) >> 1;
      S->dependencies = realloc(S->dependencies, sizeof(int) * S->maxDependencies); }
    S->dependencies[S->nDependencies++] = clause[index - 1] >> 1; }

  if ((clause[index - 1] & ACTIVE) == 0) {
    S->MARKcount++;
    clause[index - 1] |= ACTIVE;
    if (S->lemmaFile && clause[1])
      *(S->delinfo++) = (((int) (clause - S->DB) + index) << 1) + 1;
    if (clause[1 + index] == 0) return;
    markWatch (S, clause,     index, -index);
    markWatch (S, clause, 1 + index, -index); }
  while (*clause) S->false[ *(clause++) ] = MARK; }

void analyze (struct solver* S, int* clause, int index) {     // Mark all clauses involved in conflict
  markClause (S, clause, index);
  while (S->assigned > S->falseStack) {
    int lit = *(--S->assigned);
    if (S->false[ lit ] == MARK) {
      if (S->reason[ abs(lit) ]) {
        markClause (S, S->DB+S->reason[ abs(lit) ], -1);
        if (S->assigned >= S->forced)
          S->reason[ abs(lit) ] = 0; } }
    else if (S->false[ lit ] == ASSUMED && !S->RATmode) {
      S->delLit++;
      if (S->lemmaFile || S->traceFile) {
        int *tmp = S->current;
        while (*tmp != lit) tmp++;
        while (*tmp) { tmp[0] = tmp[1]; tmp++; }
        tmp[-1] = 0; } }
    S->false[ lit ] = (S->assigned < S->forced); }

  S->processed = S->assigned = S->forced; }

int propagate (struct solver* S, int init) {        // Performs unit propagation
  int *start[2], check = 0, mode = !S->prep;
  int i, lit, _lit = 0; long *watch, *_watch;
  start[0] = start[1] = S->processed;
  flip_check:;
  check ^= 1;
  while (start[check] < S->assigned) {              // While unprocessed false literals
    lit = *(start[check]++);                        // Get first unprocessed literal
    if (lit == _lit) watch = _watch;
    else watch = S->wlist[ lit ];                   // Obtain the first watch pointer
    while (*watch != END) {                         // While there are watched clauses (watched by lit)
     if ((*watch & mode) != check) {
        watch++; continue; }
     int *clause = S->DB + (*watch >> 1);	    // Get the clause from DB
     if (S->false[ -clause[0] ] ||
         S->false[ -clause[1] ]) {
       watch++; continue; }
     if (clause[0] == lit) clause[0] = clause[1];   // Ensure that the other watched literal is in front
      for (i = 2; clause[i]; ++i)                   // Scan the non-watched literals
        if (S->false[ clause[i] ] == 0) {           // When clause[j] is not false, it is either true or unset
          clause[1] = clause[i]; clause[i] = lit;   // Swap literals
          ADD_WATCH (clause[1], *watch);            // Add the watch to the list of clause[1]
          *watch = S->wlist[lit][ --S->used[lit] ]; // Remove pointer
          S->wlist[lit][ S->used[lit] ] = END;
          goto next_clause; }                       // Goto the next watched clause
      clause[1] = lit; watch++;                     // Set lit at clause[1] and set next watch
      if (!S->false[  clause[0] ]) {                // If the other watched literal is falsified,
        ASSIGN (clause[0]);                         // A unit clause is found, and the reason is set
        S->reason[abs(clause[0])] = ((long) ((clause)-S->DB)) + 1;
        if (!check) {
          start[0]--; _lit = lit; _watch = watch;
          goto flip_check; } }
      else { analyze(S, clause, 0); return UNSAT; } // Found a root level conflict -> UNSAT
      next_clause: ; } }                            // Set position for next clause
  if (check) goto flip_check;
  S->processed = S->assigned;
  return SAT; }	                                    // Finally, no conflict was found

static inline int propagateUnits (struct solver* S, int init) {
  int i;
  while (S->forced > S->falseStack) { S->false[*(--S->forced)] = 0; }
  S->forced = S->assigned = S->processed = S->falseStack;
  for (i = 0; i < S->unitSize; i++) {
    int lit = S->DB[ S->unitStack[i] ];
    S->reason[abs(lit)] = S->unitStack[i] + 1;
    ASSIGN (lit); }

  if (propagate (S, init) == UNSAT) { return UNSAT; }
  S->forced = S->processed;
  return SAT; }

// Put falsified literals at the end and returns the size under the current
// assignment: negative size means satisfied, size = 0 means falsified
int sortSize (struct solver *S, int *lemma, int diff) {
  unsigned int size = 0, last = 0, sat = 1;
  while (lemma[ last ]) {
    int lit = lemma[ last++ ];
    if (S->false[ lit ] == 0) {
      if (S->false[ -lit ]) sat = -1;
      lemma[ last-1 ] = lemma[ size ];
      lemma[ size++ ] = lit; } }
  return sat * size; }

// print the core clauses to coreFile in DIMACS format
void printCore (struct solver *S) {
  int i, j;
  for (i = 0; i < S->nClauses; i++) {
    int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
    if (lemmas[ID] & ACTIVE) S->COREcount++; }
  printf("c %i of %li clauses in core\n", S->COREcount, S->nClauses);

  if (S->coreFile) {
    fprintf(S->coreFile, "p cnf %i %i\n", S->nVars, S->COREcount);
    for (i = 0; i < S->nClauses; i++) {
      int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
      if (lemmas[ID] & ACTIVE) {
        while (*lemmas) fprintf(S->coreFile, "%i ", *lemmas++);
        fprintf(S->coreFile, "0\n"); } }
    fclose(S->coreFile); } }

// print the core lemmas to lemmaFile in DRAT format
void printProof (struct solver *S) {
  printf("c %i of %i lemmas in core using %lu resolution steps\n", S->MARKcount - S->COREcount + 1, S->Lcount, S->arcs);
  printf("c %d RAT lemmas in core; %i redundant literals in core lemmas\n", S->RATcount, S->delLit);
//  printf("c %d RAT lemmas in core; depth of proof is %d\n", S->RATcount, S->maxdepth);
/*
  int i, *sizes;
  sizes = (int *) malloc (sizeof(int) * (S->maxdepth + 1));
  for (i = 0; i <= S->maxdepth; i++) sizes[ i ] = 0;
  int checked;
  for (checked = S->nClauses; checked < S->lastLemma; checked++) {
    long ad = S->adlist[ checked ]; long d = ad & 1;
    int *lemmas = S->DB + (ad >> INFOBITS);
    if (d || lemmas[ID] % 2 == 0) continue;
    sizes[lemmas[DEPTH]]++; }
  for (i = 1; i <= S->maxdepth; i++) printf("%i (%i)\n", sizes[i], i);
*/

// NB: not yet working with forward checking
  if (S->lemmaFile) {
    S->delinfo--;
    while (*S->delinfo) {
      int offset = *S->delinfo--;
      if (offset & 1) fprintf (S->lemmaFile, "d ");
      int *lemmas = S->DB + (offset >> 1);
      int reslit = lemmas[PIVOT];
      while (*lemmas) {
        int lit = *lemmas++;
        if (lit == reslit) fprintf (S->lemmaFile, "%i ", lit); }
      lemmas = S->DB + (offset >> 1);
      while (*lemmas) {
        int lit = *lemmas++;
        if (lit != reslit) fprintf (S->lemmaFile, "%i ", lit); }
      fprintf (S->lemmaFile, "0\n"); }
    fprintf (S->lemmaFile, "0\n");
    fclose (S->lemmaFile); } }

// print the dependency graph to traceFile in TraceCheck+ format
void printTrace (struct solver *S) {
  if (S->traceFile) { int i;
    for (i = 0; i < S->nClauses; i++) {
      int *lemmas = S->DB + (S->adlist[i] >> INFOBITS);
      if (lemmas[ID] & ACTIVE) {
        fprintf(S->traceFile, "%i ", i + 1);
        while (*lemmas) fprintf (S->traceFile, "%i ", *lemmas++);
        fprintf (S->traceFile, "0 0\n"); } }
    fclose (S->traceFile); } }

void postprocess (struct solver *S) {
  printCore  (S);
  printProof (S);
  printTrace (S); }

void printDependencies (struct solver *S, int* clause) {
  if (S->traceFile) {  // This is quadratic, can be n log n
    int i, j;

    if (clause != NULL) {
      fprintf (S->traceFile, "%lu ", S->time >> 1);
      while (*clause) fprintf (S->traceFile, "%i ", *clause++); }
    else {
      fprintf (S->traceFile, "%u ", S->count - 1); }
    fprintf (S->traceFile, "0 ");

    for (i = 0; i < S->nDependencies; i++) {
      if (S->dependencies[i] != 0) {
        fprintf(S->traceFile, "%d ", S->dependencies[i]);
        for (j = i + 1; j < S->nDependencies; j++)
          if (S->dependencies[j] == S->dependencies[i])
            S->dependencies[j] = 0; } }
    fprintf(S->traceFile, "0\n"); } }

int redundancyCheck (struct solver *S, int *clause, int size, int uni) {
  int i, indegree;
  if (S->verb) { printf("c checking lemma (%i, %i) ", size, clause[PIVOT]); printClause (clause); }
  if (S->mode != FORWARD_UNSAT)
    if ((clause[ID] & ACTIVE) == 0) return SUCCEED;  // redundant?
  if (size < 0) {
    S->DB[ S->reason[abs(*clause)] - 2] |= 1;
    return SUCCEED; }

  indegree = S->arcs;
//  S->depth = clause[DEPTH];
//  if (S->maxdepth < S->depth) S->maxdepth = S->depth;

  S->RATmode = 0;
  S->nDependencies = 0;
  for (i = 0; i < size; ++i) { ASSUME(-clause[i]); }

  S->current = clause;
  if (propagate (S, 0) == UNSAT) {
    indegree = S->arcs - indegree;
    if (indegree <= 2 && S->prep == 0) {
      S->prep = 1; if (S->verb) printf("c [%li] preprocessing checking mode on\n", S->time); }
    if (indegree  > 2 && S->prep == 1) {
      S->prep = 0; if (S->verb) printf("c [%li] preprocessing checking mode off\n", S->time); }
    if (S->verb) printf("c lemma has RUP\n");
    printDependencies (S, clause);
    return SUCCEED; }

  // Failed RUP check.  Now test RAT.
  // printf("RUP check failed.  Starting RAT check.\n");
  int reslit = clause[PIVOT];
  if (S->verb)
    printf("c RUP checked failed; resolution literal %d.\n", reslit);
  int j, blocked, numCandidates = 0;
  long int reason;
  int* savedForced = S->forced;

  S->RATmode = 1;
  S->forced = S->assigned;

  // Loop over all literals to calculate resolution candidates
  for (i = -S->maxVar; i <= S->maxVar; i++) {
    if (i == 0) continue;
    // Loop over all watched clauses for literal
    for (j = 0; j < S->used[i]; j++) {
      int* watchedClause = S->DB + (S->wlist[i][j] >> 1);
      if (*watchedClause == i) { // If watched literal is in first position
        int flag = 0;
        blocked = 0;
        reason = 0;
	while (*watchedClause) {
          int lit = *watchedClause++;
          if (lit == -reslit) flag = 1;
	  else if (S->false[-lit]) { // Unless some other literal is satisfied
            if (blocked == 0 || reason > S->reason[ abs(lit) ])
              blocked = lit, reason = S->reason[ abs(lit) ]; } }

       if (blocked != 0 && reason != 0 && flag == 1) {
         analyze (S, S->DB + reason, -1); S->reason[abs(blocked)] = 0; }

       // If resolution candidate, add to list
       if (blocked == 0 && flag == 1) {
	 if (numCandidates == S->maxCandidates) {
	   S->maxCandidates = (S->maxCandidates * 3) >> 1;
	    S->resolutionCandidates = realloc(S->resolutionCandidates,
	    			      sizeof(int) * S->maxCandidates); }
	    S->resolutionCandidates[numCandidates++] = S->wlist[i][j] >> 1; } } } }

  // Check all candidates for RUP
  int flag = 1;
  for (i = 0; i < numCandidates; i++) {
    int* candidate = S->DB + S->resolutionCandidates[i];
    if (S->verb) {
      printf("c candidate: "); printClause (candidate); }
    while (*candidate) { int lit = *candidate++;
      if (lit != -reslit && !S->false[lit]) {
        ASSIGN(-lit); S->reason[abs(lit)] = 0; } }
    if (propagate (S, 0) == SAT) { flag  = 0; break; } }

  S->processed = S->forced = savedForced;
  while (S->forced < S->assigned) S->false[*(--S->assigned)] = 0;

  if (flag == 0) {
    if (S->verb) printf("c RAT check failed\n");
    return FAILED; }

  S->RATcount++;
  if (S->verb) printf("c lemma has RAT on %i\n", reslit);

  printDependencies (S, clause);
  return SUCCEED; }

int verify (struct solver *S) {
  int *delstack;
  if (S->lemmaFile) {
    delstack = (int *) malloc (sizeof(int) * S->count * 2);
    S->delinfo = delstack; }

  S->nDependencies = 0;
  S->time = S->count; // Alternative time init
  if (propagateUnits (S, 1) == UNSAT) {
      printf("c UNSAT via unit propagation on the input instance\n");
      printDependencies (S, NULL);
      postprocess (S); return UNSAT; }

  if (S->mode == FORWARD_UNSAT) printf("c start forward verification\n");
  int checked;
  int active = S->nClauses;
  for (checked = S->nClauses; checked < S->lastLemma; checked++) {
    long ad = S->adlist[ checked ]; long d = ad & 1;
    int *lemmas = S->DB + (ad >> INFOBITS);

    S->time = lemmas[ID];
    if (d) active--; else active++;
    if (S->mode == FORWARD_SAT && S->verb) printf("c %i active clauses\n", active);

    if (!lemmas[1]) { // found a unit
      int lit = lemmas[0];
      if (S->verb)
        printf("c found unit in proof %i (%li)\n", lit, d);
      if (d) {
        if (S->mode == FORWARD_SAT) {
          removeUnit (S, lit); propagateUnits (S, 0); }
        else {  // no need to remove units while checking UNSAT
          S->adlist[ checked ] = 0; continue; } }
      else {
        if (S->mode == BACKWARD_UNSAT && S->false[-lit]) { S->adlist[checked] = 0; continue; }
        else { addUnit (S, (long) (lemmas - S->DB)); } } }

    if (d && lemmas[1]) { // if delete and not unit
      if ((S->reason[abs(lemmas[0])] - 1) == (lemmas - S->DB)) {
        if (S->mode == BACKWARD_UNSAT) { // ignore pseudo unit clause deletion
          S->adlist[ checked ] = 0; }
        else if (S->mode == FORWARD_SAT) {
          removeWatch(S, lemmas, 0), removeWatch(S, lemmas, 1);
          propagateUnits (S, 0); } }
      else {
        removeWatch(S, lemmas, 0), removeWatch(S, lemmas, 1); }
      if (S->mode == FORWARD_UNSAT) continue;
      if (S->mode == BACKWARD_UNSAT) continue; }

    int size = sortSize (S, lemmas, -2 * d + 1); // after removal of watches

    if (d && S->mode == FORWARD_SAT) {
      if (size == -1) propagateUnits (S, 0);  // necessary?
      if (redundancyCheck (S, lemmas, size, 0) == FAILED) return SAT;
      continue; }

    if (d == 0 && S->mode == FORWARD_UNSAT) {
      if (redundancyCheck (S, lemmas, size, 0) == FAILED) return SAT;
      size = sortSize (S, lemmas, -2 * d + 1);
      S->nDependencies = 0; }

    if (lemmas[1])
      addWatch (S, lemmas, 0), addWatch (S, lemmas, 1);

    if (size == 0) { printf("c conflict claimed, but not detected\n"); return SAT; }  // change to FAILED?
    if (size == 1) {
      if (S->verb) printf("c found unit %i\n", lemmas[0]);
      ASSIGN (lemmas[0]); S->reason[abs(lemmas[0])] = ((long) ((lemmas)-S->DB)) + 1;
      if (propagate (S, 1) == UNSAT) goto start_verification;
      S->forced = S->processed; } }

  if (S->mode == FORWARD_SAT && active == 0) {
    postprocess (S); return UNSAT; }

  if (S->mode == BACKWARD_UNSAT) {
    printf("c ERROR: no conflict\n");
    return SAT; }


  if (S->mode == FORWARD_UNSAT) {
    printf("c ERROR: all lemmas verified, but no conflict\n");
    return SAT; }

  start_verification:;
  if (S->mode == FORWARD_UNSAT) {
    printDependencies (S, NULL);
    postprocess (S); return UNSAT; }

  printDependencies(S, NULL);
  if (S->lemmaFile) *S->delinfo++ = 0;

  if (S->mode == FORWARD_SAT) {
    printf("c ERROR: found empty clause during SAT check\n"); exit(0); }
  printf("c detected empty clause; start verification via backward checking\n");

  S->forced = S->processed;

  for (; checked >= S->nClauses; checked--) {
    long ad = S->adlist[ checked ]; long d = ad & 1; long uni = 0;
    int *clause = S->DB + (ad >> INFOBITS);

    if (ad == 0) continue; // Skip clause that has been removed from adlist
    if ( d == 0) {
      if (clause[1]) {
        removeWatch (S, clause, 0), removeWatch (S, clause, 1);
        if (S->reason[abs(clause[0])] == (clause + 1 - S->DB)) {  // use this check also for units?
          unassignUnit (S, clause[0]); } }
      else unassignUnit (S, clause[0]); }

    int size = sortSize (S, clause, 2 * d - 1); // check the diff

    if (d) {
      if (S->verb) { printf("c adding clause (%i) ", size); printClause(clause); }
      addWatch (S, clause, 0), addWatch (S, clause, 1); continue; }

    S->time = clause[ID];
    if ((S->time & ACTIVE) == 0) continue;  // If not marked, continue

    assert (size >=  1);
    int *_clause = clause + size;
    while (*_clause++) { S->delLit++; }
    clause[size] = 0;

    if (S->verb) {
      printf("c validating clause (%li, %i, %i):  ", uni, clause[PIVOT], size); printClause (clause); }

    struct timeval current_time;
    gettimeofday(&current_time, NULL);
    int seconds = (int) (current_time.tv_sec - S->start_time.tv_sec);
    if (seconds > S->timeout) printf("s TIMEOUT\n"), exit(0);

    if (redundancyCheck (S, clause, size, uni) == FAILED) return SAT;
    if (S->lemmaFile) *(S->delinfo++) = (ad >> INFOBITS) << 1; }

  postprocess (S);
  return UNSAT; }

int compare (const void *a, const void *b) {
  return (*(int*)a - *(int*)b); }

long matchClause (struct solver* S, long *clauselist, int listsize, int* input, int size) {
  int i, j;
  qsort (input, size, sizeof(int), compare);
  for (i = 0; i < listsize; ++i) {
    int *clause = S->DB + clauselist[i];
    for (j = 0; j <= size; j++)
      if (clause[j] != input[j]) goto match_next;

    long result = clauselist[ i ];
    clauselist[ i ] = clauselist[ --listsize ];
    return result;
    match_next:; }
  return 0; }

unsigned int getHash (int* input) {
  unsigned int sum = 0, prod = 1, xor = 0;
  while (*input) {
    prod *= *input; sum += *input; xor ^= *input; input++; }
  return (1023 * sum + prod ^ (31 * xor)) % BIGINIT; }

int parse (struct solver* S) {
  int tmp, active = 0, retvalue = SAT;
  int del = 0, uni = 0;
  int *buffer, bsize;

  do { tmp = fscanf (S->inputFile, " cnf %i %li \n", &S->nVars, &S->nClauses);  // Read the first line
    if (tmp > 0 && tmp != EOF) break; tmp = fscanf (S->inputFile, "%*s\n"); }  // In case a commment line was found
  while (tmp != 2 && tmp != EOF);                                              // Skip it and read next line
  int nZeros = S->nClauses;

  bsize = S->nVars*2;
  if ((buffer = (int*)malloc(bsize * sizeof(int))) == NULL) return ERROR;

  S->count      = 1;
  S->lastLemma  = 0;
//  S->depth      = 0;
//  S->maxdepth   = 0;
  S->mem_used   = 0;                  // The number of integers allocated in the DB
  S->delLit     = 0;

  long size;
  long DBsize = S->mem_used + BIGINIT;
  S->DB = (int*) malloc (DBsize * sizeof(int));
  if (S->DB == NULL) { free (buffer); return ERROR; }

  int i;
  S->maxVar   = 0;
  S->Lcount   = 0;
  int    admax     = BIGINIT;
         S->adlist = (long* ) malloc (sizeof (long ) * admax);
  long **hashTable = (long**) malloc (sizeof (long*) * BIGINIT);
  int   *hashUsed  = (int * ) malloc (sizeof (int  ) * BIGINIT);
  int   *hashMax   = (int * ) malloc (sizeof (int  ) * BIGINIT);
  for (i = 0; i < BIGINIT; i++) {
    hashUsed [ i ] = 0;
    hashMax  [ i ] = INIT;
    hashTable[ i ] = (long*) malloc (sizeof(long) * hashMax[i]); }

  int fileSwitchFlag = 0;
  size = 0;
  while (1) {
    int lit = 0; tmp = 0;
    fileSwitchFlag = nZeros <= 0;

    if (size == 0) {
      if (!fileSwitchFlag) tmp = fscanf (S->inputFile, " d  %i ", &lit);
      else tmp = fscanf (S->proofFile, " d  %i ", &lit);
      if (tmp == EOF && !fileSwitchFlag) fileSwitchFlag = 1;
      del = tmp > 0; }

    if (!lit) {
      if (!fileSwitchFlag) tmp = fscanf (S->inputFile, " %i ", &lit);  // Read a literal.
      else tmp = fscanf (S->proofFile, " %i ", &lit);
      if (tmp == EOF && !fileSwitchFlag) fileSwitchFlag = 1; }

    if (tmp == 0) {
      char ignore[1024];
      if (!fileSwitchFlag) { if (fgets (ignore, sizeof(ignore), S->inputFile) == NULL) printf("c\n"); }
      else if (fgets (ignore, sizeof(ignore), S->proofFile) == NULL) printf("c\n");
      if (S->verb) printf("c WARNING: parsing mismatch assuming a comment\n");
      continue; }

    if (abs(lit) > S->maxVar) S->maxVar = abs(lit);
    if (S->maxVar >= bsize) { bsize *= 2;
      buffer = (int*) realloc (buffer, sizeof(int) * bsize); }

    if (tmp == EOF && fileSwitchFlag) break;
    if (abs(lit) > S->nVars && !fileSwitchFlag) {
      printf("c illegal literal %i due to max var %i\n", lit, S->nVars); exit(0); }
    if (!lit) {
      if (size == 0 && !fileSwitchFlag) retvalue = UNSAT;
      if (del && S->mode == BACKWARD_UNSAT && size <= 1)  {
        del = 0; uni = 0; size = 0; continue; }
      int rem = buffer[0];
      buffer[ size ] = 0;
//      printf("c "); printClause(buffer);
      unsigned int hash = getHash (buffer);
      if (del || uni) {
        if (S->delete) {
//          int  count = 0;
          long match = 0;
//          for (;;) {
            match = matchClause (S, hashTable[hash], hashUsed[hash], buffer, size);
            if (match == 0) {
//              if (count) break;
              printf("c MATCHING ERROR: "); printClause (buffer); exit (0); }
            if (S->mode == FORWARD_SAT) S->DB[ match - 2 ] = rem;
//            count++;
            hashUsed[hash]--;
            active--;
            if (S->lastLemma == admax) { admax = (admax * 3) >> 1;
              S->adlist = (long*) realloc (S->adlist, sizeof(long) * admax); }
            S->adlist[ S->lastLemma++ ] = (match << INFOBITS) + 1; }
//          if (count > 1) {
//            printf("c WARNING: %i times removed ", count); printClause(buffer); } }
        if (del) { del = 0; uni = 0; size = 0; continue; } }

      if (S->mem_used + size + EXTRA > DBsize) { DBsize = (DBsize * 3) >> 1;
	S->DB = (int *) realloc(S->DB, DBsize * sizeof(int)); }
      int *clause = &S->DB[S->mem_used + EXTRA - 1];
      if (size != 0) clause[PIVOT] = buffer[0];
      clause[ID] = 2 * S->count; S->count++;
//      clause[DEPTH] = 0;
      if (S->mode == FORWARD_SAT) if (nZeros > 0) clause[ID] |= ACTIVE;
//      printf("c "); printClause(buffer);

      qsort (buffer, size, sizeof(int), compare);
      for (i = 0; i < size; ++i) { clause[ i ] = buffer[ i ]; } clause[ i ] = 0;
      S->mem_used += size + EXTRA;

      hash = getHash (clause);
      if (hashUsed[hash] == hashMax[hash]) { hashMax[hash] = (hashMax[hash] * 3) >> 1;
        hashTable[hash] = (long *) realloc(hashTable[hash], sizeof(long*) * hashMax[hash]); }
      hashTable[ hash ][ hashUsed[hash]++ ] = (long) (clause - S->DB);

      active++;
      if (S->lastLemma == admax) { admax = (admax * 3) >> 1;
        S->adlist = (long*) realloc (S->adlist, sizeof(long) * admax); }
      S->adlist[ S->lastLemma++ ] = (((long) (clause - S->DB)) << INFOBITS) + 2 * uni;
      if (nZeros <= 0) S->Lcount++;

      if (!nZeros) S->lemmas   = (long) (clause - S->DB);    // S->lemmas is no longer pointer
      size = 0; del = 0; uni = 0; --nZeros; }                // Reset buffer
   else buffer[ size++ ] = lit; }                            // Add literal to buffer

  if (S->mode == FORWARD_SAT && active) {
    printf("c WARNING: %i clauses active if proof succeeds\n", active);
    for (i = 0; i < BIGINIT; i++) {
      int j;
      for (j = 0; j < hashUsed[i]; j++) {
        printf("c ");
        int *clause = S->DB + hashTable [i][j];
        printClause (clause);
        if (S->lastLemma == admax) { admax = (admax * 3) >> 1;
            S->adlist = (long*) realloc (S->adlist, sizeof(long) * admax); }
        S->adlist[ S->lastLemma++ ] = (((int)(clause - S->DB)) << INFOBITS) + 1; } } }

  S->DB = (int *) realloc(S->DB, S->mem_used * sizeof(int));

  for (i = 0; i < BIGINIT; i++) free (hashTable[i]);
  free (hashTable);
  free (hashUsed);
  free (hashMax);
  free (buffer);

  printf ("c finished parsing\n");
//  printf ("c finished parsing. average lifetime of lemmas is %.3f\n", 0);

  int n = S->maxVar;
  S->falseStack = (int*) malloc((n + 1) * sizeof(int)); // Stack of falsified literals -- this pointer is never changed
  S->forced     = S->falseStack;      // Points inside *falseStack at first decision (unforced literal)
  S->processed  = S->falseStack;      // Points inside *falseStack at first unprocessed literal
  S->assigned   = S->falseStack;      // Points inside *falseStack at last unprocessed literal
  S->reason     = (long*) malloc((    n + 1) * sizeof(long)); // Array of clauses
  S->used       = (int *) malloc((2 * n + 1) * sizeof(int )); S->used  += n; // Labels for variables, non-zero means false
  S->max        = (int *) malloc((2 * n + 1) * sizeof(int )); S->max   += n; // Labels for variables, non-zero means false
  S->false      = (int *) malloc((2 * n + 1) * sizeof(int )); S->false += n; // Labels for variables, non-zero means false

  S->arcs      = 0;
  S->RATmode   = 0;
  S->RATcount  = 0;
  S->MARKcount = 0;
  S->COREcount = 0;

  S->maxCandidates = CANDIDATE_INIT_SIZE;
  S->resolutionCandidates = (int*) malloc(sizeof(int) * S->maxCandidates);
  for (i = 0; i < S->maxCandidates; i++) S->resolutionCandidates[i] = 0;

  S->maxDependencies = DEPENDENCIES_INIT_SIZE;
  S->dependencies = (int*) malloc(sizeof(int) * S->maxDependencies);
  for (i = 0; i < S->maxDependencies; i++) S->dependencies[i] = 0;

  for (i = 1; i <= n; ++i) { S->reason    [i]           =    0;
                             S->falseStack[i]           =    0;
	                     S->false[i] = S->false[-i] =    0;
                             S->used [i] = S->used [-i] =    0;
                             S->max  [i] = S->max  [-i] = INIT; }

  S->wlist = (long**) malloc (sizeof(long*) * (2*n+1)); S->wlist += n;

  for (i = 1; i <= n; ++i) { S->wlist[ i] = (long*) malloc (sizeof(long) * S->max[ i]); S->wlist[ i][0] = END;
                             S->wlist[-i] = (long*) malloc (sizeof(long) * S->max[-i]); S->wlist[-i][0] = END; }

  S->unitSize  = 0;
  S->unitStack = (long *) malloc (sizeof(long) * n);

  for (i = 0; i < S->nClauses; i++) {
    int *clause = S->DB + (S->adlist[i] >> INFOBITS);
    if (clause[0] == 0) {
      printf ("c formula contains empty clause\n");
      if (S->coreFile) {
        fprintf (S->coreFile, "p cnf 0 1\n 0\n");
        close (S->coreFile); }
      if (S->lemmaFile) {
        fprintf (S->lemmaFile, "0\n");
        close (S->lemmaFile); }
      return UNSAT; }
    if (clause[1]) { addWatch (S, clause, 0); addWatch (S, clause, 1); }
    else if (S->false[  clause[0] ]) {
      printf ("c found complementary unit clauses\n");
      if (S->coreFile) {
        fprintf (S->coreFile, "p cnf %i 2\n%i 0\n%i 0\n", abs(clause[0]), clause[0], -clause[0]);
        close (S->coreFile); }
      if (S->lemmaFile) {
        fprintf (S->lemmaFile, "0\n");
        close (S->lemmaFile); }
      return UNSAT; }
    else if (!S->false[ -clause[0] ]) {
      addUnit (S, (long) (clause - S->DB));
      ASSIGN (clause[0]); }
  }
  return retvalue; }

void freeMemory(struct solver *S) {
  free (S->DB);
  free (S->falseStack);
  free (S->reason);
  free (S->adlist);
  int i; for (i = 1; i <= S->maxVar; ++i) { free (S->wlist[i]); free (S->wlist[-i]); }
  free (S->used  - S->maxVar);
  free (S->max   - S->maxVar);
  free (S->false - S->maxVar);
  free (S->wlist - S->maxVar);
  free (S->resolutionCandidates);
  free (S->dependencies);
  return; }

void printHelp ( ) {
  printf("usage: drat-trim [INPUT] [<PROOF>] [<option> ...]\n\n");
  printf("where <option> is one of the following\n\n");
  printf("  -h          print this command line option summary\n");
  printf("  -c CORE     prints the unsatisfiable core to the file CORE\n");
  printf("  -l LEMMAS   prints the core lemmas to the file LEMMAS\n");
  printf("  -r TRACE    resolution graph in TRACECHECK format\n\n");
  printf("  -t <lim>    time limit in seconds (default %i)\n", TIMEOUT);
  printf("  -u          default unit propatation (i.e., no core-first)\n");
  printf("  -f          forward mode for UNSAT\n");
  printf("  -v          more verbose output\n");
  printf("  -p          run in plain mode (i.e., ignore deletion information)\n\n");
  printf("  -S          run in SAT check mode (forward checking)\n\n");
  printf("and input and proof are specified as follows\n\n");
  printf("  INPUT       input file in DIMACS format\n");
  printf("  PROOF       proof file in DRAT format (stdin if no argument)\n\n");
  exit(0); }

int main (int argc, char** argv) {
  struct solver S;

  S.inputFile = NULL;
  S.proofFile = stdin;
  S.coreFile  = NULL;
  S.lemmaFile = NULL;
  S.traceFile = NULL;
  S.timeout   = TIMEOUT;
  S.mask      = 0;
  S.verb      = 0;
  S.prep      = 0;
  S.mode      = BACKWARD_UNSAT;
  S.delete    = 1;
  gettimeofday(&S.start_time, NULL);

  int i, tmp = 0;
  for (i = 1; i < argc; i++) {
    if        (argv[i][0] == '-') {
      if      (argv[i][1] == 'h') printHelp ();
      else if (argv[i][1] == 'c') S.coreFile  = fopen (argv[++i], "w");
      else if (argv[i][1] == 'l') S.lemmaFile = fopen (argv[++i], "w");
      else if (argv[i][1] == 'r') S.traceFile = fopen (argv[++i], "w");
      else if (argv[i][1] == 't') S.timeout   = atoi(argv[++i]);
      else if (argv[i][1] == 'u') S.mask      = 1;
      else if (argv[i][1] == 'v') S.verb      = 1;
      else if (argv[i][1] == 'p') S.delete    = 0;
      else if (argv[i][1] == 'f') S.mode      = FORWARD_UNSAT;
      else if (argv[i][1] == 'S') S.mode      = FORWARD_SAT; }
    else {
      tmp++;
      if (tmp == 1) {
        S.inputFile = fopen (argv[1], "r");
        if (S.inputFile == NULL) {
          printf("c error opening \"%s\".\n", argv[i]); return ERROR; } }

      else if (tmp == 2) {
        S.proofFile = fopen (argv[2], "r");
        if (S.proofFile == NULL) {
          printf("c error opening \"%s\".\n", argv[i]); return ERROR; } } } }

  if (tmp == 1) printf ("c reading proof from stdin\n");
  if (tmp == 0) printHelp ();

  int parseReturnValue = parse(&S);

  fclose (S.inputFile);
  fclose (S.proofFile);
  int sts = ERROR;
  if       (parseReturnValue == ERROR)    printf ("s MEMORY ALLOCATION ERROR\n");
  else if  (parseReturnValue == UNSAT)    printf ("c trivial UNSAT\ns VERIFIED\n");
  else if  ((sts = verify (&S)) == UNSAT) printf ("s VERIFIED\n");
  else printf ("s NOT VERIFIED\n")  ;
  freeMemory (&S);
  return (sts != UNSAT); // 0 on success, 1 on any failure
}
