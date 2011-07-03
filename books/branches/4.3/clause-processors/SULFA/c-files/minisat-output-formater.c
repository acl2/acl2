
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

int digit(char x) {
  return (x >= '0') && (x <= '9');
}

void write_time_if_present(char *char_buff) {
  if (strncmp(char_buff, "CPU time",8) == 0) {
    int i;
    printf("(time \"");
    for (i=0; char_buff[i] != 0; i++) {
      if (char_buff[i] == '.' || digit(char_buff[i]))
        putchar(char_buff[i]);        
    }
    printf("\")\n");
  }
}

void write_unsat_if_present(char *char_buff) {
    if (strcmp(char_buff, "UNSAT\n") == 0) {
      /* Instance is unsatisfiable */
      printf("(unsat)\n");
    }
}

char buffered_getc(int *in_bufn, char *in_buff, FILE *file) {
  if (in_buff[*in_bufn] != 0) {
    char ans = in_buff[*in_bufn];
    *in_bufn += 1;
    return ans;
  }
  return fgetc(file);
}

void write_instance(int *in_bufn, char *in_buff, FILE *file) {
  char char_buff[100];
  char curr_char;
  int bufn=0;
  int negative=0;
  long curr_num=1;
  long read_num;

  curr_char = buffered_getc(in_bufn, in_buff, file);

  /* printf("Checking: %c\n", curr_char); */

  while (curr_char == ' ' || curr_char == '\n' || 
         curr_char == '-' ||
         digit(curr_char)) {

    if (curr_char == ' ') {
      if (bufn != 0) {
        char_buff[bufn]=0;
        /* printf("Checking: %s\n", char_buff);*/
        
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
      }
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
    curr_char = buffered_getc(in_bufn, in_buff, file);
  }
}

void write_instance_if_present(int *in_bufn, char *in_buff, FILE *file) {
    if (strcmp(in_buff, "SAT\n") == 0) {
      /* Instance is unsatisfiable */
      printf("(sat\n");
      write_instance(in_bufn, in_buff, file);
      printf(")\n");
    }
}

int main(int nargs, char **argc) {
  FILE *file;
  char curr_char;
  char char_buff[100];
  int bufn=0;

  if (nargs <= 1) {
    printf("(Error \"Input file required\")\n");
    return 1;
  }

  file = fopen(argc[1], "r");


  curr_char = fgetc(file);  

  bufn=0;
  
  while ((curr_char != '\n') && (curr_char != EOF) && (bufn < 50)) {
    char_buff[bufn]=curr_char;
    bufn++;
    curr_char = fgetc(file);
  }

  char_buff[bufn] = curr_char;
  char_buff[bufn+1]=0;
  bufn++;

  /* printf("Checking: %s\n", char_buff); */
  write_unsat_if_present(char_buff);
  write_instance_if_present(&bufn, char_buff, file);

  fclose(file);

  return 0;
}


