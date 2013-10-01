
#include <stdio.h>

int main(int nargs, char **argc) {
  FILE *cnf_file;
  char curr_char;

  if (nargs <= 3) {
    printf("Not enough arguments.  Need an input file, the number ");
    printf("of variables and the number of clauses\n");
    return 1;
  }

  // Start by printing out the number of variables
  // and clauses.
  fputs("\n", stdout);
  fputs("p cnf ", stdout);
  fputs(argc[2], stdout);
  fputs(" ", stdout);
  fputs(argc[3], stdout);
  fputs("\n", stdout);

  // Now we print out the clause list
  cnf_file = fopen(argc[1], "r");

  if (cnf_file == NULL) {
    perror("Error opening input file\n");
    return 1;
  }

  curr_char = fgetc(cnf_file);
  while (curr_char != EOF) {
    
    if (curr_char == '(') {
      // Now we've hit a clause
      curr_char = fgetc(cnf_file);
      
      while (curr_char != ')') {
        fputc(curr_char, stdout);
        curr_char = fgetc(cnf_file);
      }
      
      fputc(32, stdout);
      fputc('0', stdout);
      fputc('\n', stdout);
    }
    curr_char = fgetc(cnf_file);  
  }

  fputc('\n', stdout);
  return 0;
}
