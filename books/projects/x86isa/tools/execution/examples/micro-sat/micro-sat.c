// Author: Marijn Heule
// File created for simulation on the x86 ISA model.
// micro-sat.c   last edit: August 30, 2012 
 
#include <stdio.h> 
 
#define END        -9 
#define MEM_MAX     100000000 
#define MARK        2 
#define UNSAT       0 
#define SAT         1 
 
struct solver { // The variables in the struct are described in the parser 
  int  *DB, nVars, nClauses, mem_used, mem_fixed, maxLemmas, nLemmas, 
       restarts, nConflicts, *model, *reason, *falseStack, *false, *first, 
       *heap, heapSize, *lookup, *score, *forced, *processed, *assigned; }; 
 
#define SET_MARK(a)	{ int lit = (a);        \
                          if (S->false[ lit ] != MARK) { \
			    S->score[ abs(lit) ] = (3 * S->score[ abs(lit) ] + (S->nConflicts << 5)) >> 2; \
			    if (S->lookup[abs(lit)] != END) heapUp(S, abs(lit)); } \
                          S->false[ lit ] = MARK; } 
#define ASSIGN(a,r)	{ S->false[-(a)] = 1 + 5*forced; \
                          *(S->assigned++) = -(a); \
                          S->reason[abs(a)] = 1 + (int) ((r)-S->DB); \
                          S->model[abs(a)] = ((a)>0); } 
#define ASSIGN_DEC(a)	{ S->false[-(a)] = 1; \
                          *(S->assigned++) = -(a); \
                          S->reason[abs(a)] = 0; } 
#define UNASSIGN(a)     { int lit = (a); S->false[ lit ] = 0; \
                          if (S->lookup[abs(lit)] == END) { \
                            S->lookup[abs(lit)] = ++S->heapSize; \
                            heapUp(S, abs(lit)); } } 
#define ADD_WATCH(l,m)  { S->DB[(m)] = S->first[(l)]; S->first[(l)] = (m); } 
 
int* getMemory (struct solver *S, int mem_size) { 
  int *store = (S->DB + S->mem_used); 
  S->mem_used += mem_size; 
  return store; } 
 
int* addClause (struct solver *S, int* input, int size) { 
  if (size > 1) { ADD_WATCH (input[0], S->mem_used); ADD_WATCH (input[1], S->mem_used + 1); } 
  int i, *clause = getMemory (S, size + 3) + 2; 
  for (i = 0; i < size; ++i) { clause[ i ] = input[ i ]; } clause[ i ] = 0; 
  return clause; } 
 
void reduceDB (struct solver* S) {         // Removes less useful lemmas from DB 
  int *head    = (S->DB + S->mem_fixed);   // Place head at the start of the lemmas 
  int *tail    = (S->DB + S->mem_used);    // Place tail at the end of the lemmas 
  S->maxLemmas = (S->maxLemmas * 9) >> 3;  // Allow more lemmas in the future 
  S->mem_used  = S->mem_fixed;             // Virtually remove all lemmas 
  S->nLemmas   = 0;                        // Reset the number of lemmas 
 
  int i; for (i = -S->nVars; i <= S->nVars; ++i) {                // Loop over the variables 
    if (i == 0) continue; int *watch = &S->first[ i ];            // Get the pointer to the first watched clause 
    while (*watch != END)                                         // As long as there are watched clauses 
      if (*watch < S->mem_fixed) watch = (S->DB + *watch);        // Remove the watch if it points to a lemma 
      else                      *watch =  S->DB[  *watch ]; }     // Otherwise (meaning an input clause) go to next watch 
 
  while (head < tail) {                                           // While the old memory contains lemmas 
    int size = 0, count = 0, *lemma = head+2;                     // Get the lemma to which the head is pointing 
    while (*lemma) {                                    size++;   // Count the number of literals 
      if ((*lemma > 0) == S->model[ abs(*(lemma++)) ]) count++; } // Count the number of satisfied literals 
    if (count < 4) { addClause (S, head+2, size); S->nLemmas++; } // If the latter is smaller than four, add it back 
    head = lemma+1; } }                                           // Move the head to the next position after the lemma 
 
void heapRemoveTop (struct solver* S) {                    // Removes the top of the binary heap 
  S->lookup[ S->heap[0] ] = END;                           // Stamp the lookup of the top of the heap as out 
  int last  = S->heap[S->heapSize--];                      // Obtain the last element in the heap 
  int score = S->score[last], p = 0, c = 1;                // Obtain the score of that element, set p(arent) 
  while (c <= S->heapSize) {                               // While there are children in the heap 
    if ((S->score[S->heap[c]] < S->score[S->heap[c+1]]) && // If the score of the left child is smaller AND 
        (c < S->heapSize)) c++;                            // A right child exists, point to the right child 
    if  (S->score[S->heap[c]] < score) break;              // Break if the score of pointed child is smaller 
    S->heap[p] = S->heap[c];                               // Swap last and its current child 
    S->lookup[S->heap[c]] = p; p = c; c = (c<<1)+1; }	   // Update the heap lookup table and update the position 
  S->heap[p] = last; S->lookup[last] = p; }                // Set the new position in the heap and update the lookup 
 
void heapUp (struct solver* S, int var) {		   // Moves a var(iable) up in the binary heap 
  int score = S->score[var], p = S->lookup[var];           // Obtain the score and the position of var in the heap 
  while (p && (S->score[ S->heap[(p-1)>>1] ] < score)) {   // While its score is larger than the score of its parent 
    S->heap[p] = S->heap[(p-1)>>1];                        // Swap var and its parent 
    S->lookup[S->heap[p]] = p; p = (p-1)>>1; }             // Update the heap lookup table and update the position 
  S->heap[p] = var; S->lookup[var] = p; }                  // Set the new position in the heap and update the lookup 
 
int implied (struct solver* S, int lit) {                  // Check if lit(eral) is implied by MARK literals 
  if (S->false[lit] > MARK) return (S->false[lit] & MARK); // If checked before return old result 
  if (!S->reason[abs(lit)]) return 0;                      // In case lit is a decision, it is not implied 
  int *p = (S->DB + S->reason[abs(lit)] - 1);              // Get the reason of lit(eral) 
  while (*(++p))                                           // While there are literals in the reason 
    if ((S->false[*p] ^ MARK) && !implied(S, *p)) {        // Recursively check if non-MARK literals are implied 
      S->false[lit] = 5; return 0; }                       // Return not implied (stamp 5 means not implied) 
  S->false[lit] = 6; return 1; }                           // Return implied (stamp 6 means implied) 
 
int* analyze (struct solver* S, int* clause) {     // Compute a resolvent from falsified clause 
  S->nLemmas++; S->restarts++; S->nConflicts++;    // Bump restarts and bump maximum score 
 
  while (*clause) SET_MARK(*(clause++));           // MARK all literals in falsified clause 
  while (S->reason[ abs(*(--S->assigned)) ]) {     // Loop on variables on falseStack 
    if (S->false[ *S->assigned ] == MARK) {        // If the tail of the stack is MARK 
      int *check = S->assigned;                    // Pointer to check if first-UIP is reached 
      while (S->false[ *(--check) ] != MARK)	   // Check for a MARK literal before decision 
        if (!S->reason[ abs(*check) ]) goto build; // Otherwise it is the first-UIP so break 
      clause=(S->DB + S->reason[abs(*S->assigned)]); // Get the reason and ignore first literal 
      while (*clause) SET_MARK(*(clause++)); }     // MARK all literals in reason 
    UNASSIGN(*S->assigned); }                      // Unassign the tail of the stack 
 
  build:; int buffer[ 4 ], size = 0; 
  int *p = S->assigned;                            // Loop from tail to front 
  while (p >= S->forced) {                         // Only literals on the stack can be MARK 
    if ((S->false[*p] == MARK) && !implied (S,*p)) // If MARK and not implied by other MARK literals 
      buffer[ size++ ] = *p;                       // Add literal to conflict clause 
    if ((size == 1) && !S->reason[ abs(*p) ]) 
      S->processed = p;                            // Set backjump point (in the search) 
    S->false[ *(p--) ] = 1; }                      // Reset the MARK flag for all variables on the stack 
 
  while (S->assigned > S->processed) 
    UNASSIGN(*(S->assigned--));                    // Unassign all lits between tail & head 
  UNASSIGN(*S->assigned);                          // Assigned now equal to processed 
  return addClause (S, buffer, size); }            // Add new conflict clause to redundant DB 
 
int propagate (struct solver* S) {                 // Performs unit propagation 

  int check =  *(S->processed);

  int abscheck = abs(check);

  int forced = S->reason[ abscheck ];	           // Initialize forced flag 

  while (S->processed < S->assigned) {             // While unprocessed false literals 
    int  lit   = *(S->processed++);                // Get first unprocessed literal 
    int* watch = &S->first[ lit ];                 // Obtain the first watch pointer 
    while (*watch != END) {                        // While there are watched clauses (watched by lit) 
      int i, *clause = (S->DB + *watch + 1);	   // Get the clause from DB 
      if (!clause[-2]) clause++;                   // Set the pointer to the first literal in the clause 
      if (clause[0] == lit) clause[0] = clause[1]; // Ensure that the other watched literal is in front 
      for (i = 2; clause[i]; ++i)                  // Scan the non-watched literals 
        if (!S->false[ clause[i] ]) {              // When clause[j] is not false, it is either true or unset 
          clause[1] = clause[i]; clause[i] = lit;  // Swap literals 
          int store = *watch;                      // Store the old watch 
          *watch =  S->DB[ *watch ];               // Remove the watch from the list of lit 
          ADD_WATCH (clause[1], store);            // Add the watch to the list of clause[1] 
          goto next_clause; }                      // Goto the next watched clause 
      clause[1] = lit; watch = (S->DB + *watch);   // Set lit at clause[1] and set next watch 
      if ( S->false[ -clause[0] ]) continue; 	   // If the other watched literal is satisfied continue 
      if (!S->false[  clause[0] ]) {               // If the other watched literal is falsified, 
        ASSIGN (clause[0], clause); }              // A unit clause is found, and the reason is set 
      else if (forced) return UNSAT;               // Found a root level conflict -> UNSAT 
      else { int *lemma = analyze (S, clause);	   // Analyze the conflict return a conflict clause 
        ASSIGN (lemma[ 0 ], lemma);                // Assign the conflict clause as a unit 
        forced = !lemma[1]; break; }               // In case a unit clause is found, set forced flag 
      next_clause: ; } }                           // Set position for next clause 
  if (forced) S->forced = S->processed;	           // Set S->forced if applicable 
  return SAT; }	                                   // Finally, no conflict was found 
 
int luby (int x) {                                 // Find the next number in the Luby sequence 
    int size, seq; 
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1); 
    while (size-1 != x) { size = (size-1)>>1; seq--; x = x % size; } 
    return seq; } 
 
int solve (struct solver *S) { 
  int restarts = 0, shift = luby (restarts); 
  for (;;) {                                  // Main loop 

    if (S->assigned > S->processed)
    if (propagate (S) == UNSAT) return UNSAT; // UP returns UNSAT for root level conflict 
 
    if (S->restarts > (100 << shift) || S->nLemmas > S->maxLemmas) {          // After more than (100 << shift) conflicts 
      while (S->assigned > S->forced) UNASSIGN(*(--S->assigned));             // Remove all false lits from falseStack 
      S->processed = S->forced; S->restarts = 0; shift = luby (++restarts); } // Reset pointers and restart counter 
 
    if (S->nLemmas > S->maxLemmas) reduceDB (S);                        // Reduce the DB when it contains too many lemmas 
 
    while (S->heapSize) {                                               // Get the next decision from the heap 
      if (!S->false[ S->heap[0] ] && !S->false[ -S->heap[0] ] ) break;  // If the top of the heap is unassigned 
      heapRemoveTop (S); }                                              // Otherwise remove the top from the heap 
    if (!S->heapSize) return !UNSAT;                                    // A solution is found when the heap is empty 
    ASSIGN_DEC (S->model[ S->heap[0] ] ? S->heap[0] : -S->heap[0]); } } // Assign decision based on current model 
 
int parse (struct solver* S, char* filename) { 
  int forced = 1, tmp, i; 
  S->nVars = 4;
  S->nClauses = 8;
  int nZeros = S->nClauses, buffer [4], size = 0, n = S->nVars;   // Make a local buffer 
 
  S->mem_used   = 0;                  // The number of integers allocated in the DB 
  S->nLemmas    = 0;                  // The number of learned clauses -- redundant means learned 
  S->nConflicts = 0;                  // Under of conflicts which is used to updates scores 
  S->restarts   = 0;                  // Counter used for deciding when to restart 
  S->maxLemmas  = 2+S->nClauses >> 2; // The maximum number of lemmas 
  S->model      = getMemory (S, n+1); // Full assignment of the (Boolean) variables (initially set to false) 
  S->score      = getMemory (S, n+1); // Variable score (based on involvement in recent conflicts). 
  S->heap       = getMemory (S, n  ); // Binary heap of variables sorted by S->score 
  S->heapSize   = n-1;                // Size of the heap 
  S->lookup     = getMemory (S, n+1); // Lookup table for the position of a variable in the heap 
  S->reason     = getMemory (S, n+1); // Array of clauses 
  S->falseStack = getMemory (S, n+1); // Stack of falsified literals -- this pointer is never changed 
  S->forced     = S->falseStack;      // Points inside *falseStack at first decision (unforced literal) 
  S->processed  = S->falseStack;      // Points inside *falseStack at first unprocessed literal 
  S->assigned   = S->falseStack;      // Points inside *falseStack at last unprocessed literal 
  S->false      = getMemory (S, 2*n+1); S->false += n; // Labels for variables, non-zero means false 
  S->first      = getMemory (S, 2*n+1); S->first += n; // Offset of the first watched clause 
  S->DB[ S->mem_used++ ] = 0;         // Make sure there is a 0 before the clauses are loaded. 
 

  S->reason[0]=0;
  for (i = 1; i <= n; ++i) { S->heap[i-1] = i; S->lookup[i] = i-1; S->model[i] = 0; 
    S->score[i] = 1; S->falseStack[i-1]=0; S->reason[i] = 0; S->false[i] = S->false[-i] = 0; S->first[i] = S->first[-i] = END; } 
 
i=0; buffer[i++]=1 ;buffer[i++]=2 ;buffer[i++]=-3 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=-1 ;buffer[i++]=-2 ;buffer[i++]=3 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=2 ;buffer[i++]=3 ;buffer[i++]=-4 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=-2 ;buffer[i++]=-3 ;buffer[i++]=4 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=-1 ;buffer[i++]=-3 ;buffer[i++]=-4 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=1 ;buffer[i++]=3 ;buffer[i++]=4 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=-1 ;buffer[i++]=2 ;buffer[i++]=4 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
i=0; buffer[i++]=1 ;buffer[i++]=-2 ;buffer[i++]=-4 ; addClause (S, buffer, i); if (!i || ((i == 1) && S->false[ buffer[0] ])) return UNSAT; if ((i == 1) && !S->false[ -buffer[0] ]) { ASSIGN (buffer[0], buffer); }
 
  S->mem_fixed = S->mem_used; // From now on, only redundant clauses will be added 
  return SAT; } 
 
int memory[ MEM_MAX ]; 
 
int main (int argc, char** argv) { 
  struct solver S; /*int memory[ MEM_MAX ];*/ S.DB = memory; 
  int sol;
 
  /* if (parse (&S, argv[1]) == UNSAT) printf("s UNSATISFIABLE\n");  Parse the file in argv[1]  */
  /* else if     (solve (&S) == UNSAT) printf("s UNSATISFIABLE\n");  */
  /* else                              printf("s SATISFIABLE\n")  ;  */

  if (parse (&S, argv[1]) == UNSAT) sol = 0;
  else if     (solve (&S) == UNSAT) sol = 0;
  else                              sol = 1;

  } 
