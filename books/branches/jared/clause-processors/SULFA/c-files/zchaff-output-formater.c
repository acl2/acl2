
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

int digit(char x) {
  return (x >= '0') && (x <= '9');
}

void write_time(FILE *cnf_file) {
  char char_buff[200];
  char curr_char;
  int bufn=0;
  int i;
  
  while (curr_char != EOF) {
    bufn=0;
    while ((curr_char != '\n') && (curr_char != EOF)) {
      if (bufn < 195) {
        char_buff[bufn]=curr_char;
        bufn++;
      } 
      curr_char = fgetc(cnf_file);
    }
    char_buff[bufn]=0;

    //printf("testing, %s\n", char_buff);
    if (strncmp(char_buff, "Total Run Time",14) == 0) {
      //printf("found it, %s\n", char_buff);
      for (i=0; i<bufn; i++) {
        if (char_buff[i] == '.' || digit(char_buff[i]))
          putchar(char_buff[i]);        
      }
      return;
    }
    curr_char = fgetc(cnf_file);
  }
  printf("-1"); // no time found
}

  

void write_instance(FILE *cnf_file) {
  char char_buff[100];
  char curr_char;
  int bufn=0;
  int negative=0;
  long curr_num=1;
  long read_num;

  curr_char = fgetc(cnf_file);

  while (curr_char == ' ' ||
         curr_char == '-' ||
         digit(curr_char)) {

    if (curr_char == ' ') {
      char_buff[bufn]=0;
      read_num = atol(char_buff);
      
      while (curr_num < read_num) {
        /* Some numbers may not be specified in the
           satisfying instance.  In that case, I assume
           their value is irrelevant */
        printf("X ");
        curr_num++;
      }
 
      if (curr_num != read_num) {
        /* I assume that all the numbers come in order */
        printf("Error: Read in a number out of sequence: %s\n", char_buff);
        exit(1);
      }

      /* Now we print out the value of the corresponding number */
      if (negative == 1) {
        printf("nil ");
      } else {
        printf("t ");
      }
      curr_num++;
      bufn = 0;
      negative=0;
    } else if (curr_char == '-') {
      negative=1;
    } else if (bufn < 10) {
      char_buff[bufn] = curr_char;
      bufn++;
    } else {
      /* Note: I should be doing something more intelligent here but
         it's too late to print out a good error message */
      printf("Error: Number is too big to be read\n");
      exit(1);
    }
    curr_char = fgetc(cnf_file);
  }
}


int main(int nargs, char **argc) {
  FILE *cnf_file;
  char curr_char;
  char char_buff[100];
  int bufn=0;

  if (nargs <= 1) {
    printf("(Error \"No input file name given\")\n");
    return 1;
  }

  cnf_file = fopen(argc[1], "r");

  curr_char = fgetc(cnf_file);

  while (curr_char != EOF) {
    /* printf(".\n"); */
    bufn=0;
    while ((curr_char != '\n') && (curr_char != EOF)) {
      if (bufn < 50) {
        char_buff[bufn]=curr_char;
        bufn++;
      } 
      curr_char = fgetc(cnf_file);
    }

    char_buff[bufn]=0;
    /* printf("Checking:  %s, %d\n", char_buff, strcmp(char_buff, "Instance Satisfiable")); */

    if (strcmp(char_buff, "Instance Unsatisfiable") == 0) {
      /* Instance is unsatisfiable */
      printf("(unsat)\n");

      printf("(time \"");
      write_time(cnf_file);
      printf("\")\n");
      fclose(cnf_file);
      return 0;
    }
    if (strcmp(char_buff, "Instance Satisfiable") == 0) {
      /* Instance is satisfiable */
      printf("(sat ");
      write_instance(cnf_file);
      printf(")\n");

      printf("(time \"");
      write_time(cnf_file);
      printf("\")\n");
      fclose(cnf_file);
      return 0;
    }
    if (curr_char != EOF) curr_char = fgetc(cnf_file);
  }

  printf("(Error \"no result\")\n");
  fclose(cnf_file);
  return 1;
}
