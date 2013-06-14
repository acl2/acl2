

/* A simple program that puts the SMT benchmark into a 
   format that is readable by ACL2's read-object */

#include <stdio.h>
#include <ctype.h>

int is_smt_special(char c) {
  return isspace(c) || (c == '(') || (c == ')') ||
    (c == '{') || (c == '}') ||
    (c == '[') || (c == ']');
}

int is_number_str(char* char_buff) {
  int n = 0;
  int ans = 1;

  while (char_buff[n] != 0) {
    if (!isdigit(char_buff[n])) {
      ans = 0;
    }
    n += 1;
  }
  return ans;
}
     
void print_char_buff(char* char_buff) {
  if (char_buff[0] == 0) {
    return;
  } else if (is_number_str(char_buff)) {
    fputs(char_buff, stdout);
  } else {
    fputs("|", stdout);
    fputs(char_buff, stdout);
    fputs("|", stdout);
  }
}

char my_getchar() {
  return getchar();
}

int main(int nargs, char **argc) {
  char char_buff[200];
  char curr_char;
  int bufn=0;

  curr_char = my_getchar();
  while (curr_char != EOF) {

    bufn=0;
    while (!is_smt_special(curr_char)) {
      char_buff[bufn] = curr_char;
      bufn++;
      curr_char = my_getchar();
    }
    char_buff[bufn] = 0;

    if (curr_char == '[') {
      fputs("(", stdout);
      print_char_buff(char_buff);
      fputs(" ", stdout);

      curr_char = my_getchar();
      while (curr_char != ']') {
        if (curr_char == ':') {
          fputs(" ", stdout);
        } else {
          putchar(curr_char);
        }
        curr_char = my_getchar();
      }
      fputs(")", stdout);        
    } else if (curr_char == '{') {
      fputs("\"comment\"", stdout);
      while (curr_char != '}') {
        curr_char = my_getchar();
      }
    } else {
      if (char_buff[0] != 0) {
        print_char_buff(char_buff);
      }
      putchar(curr_char);
    }
    curr_char = my_getchar();
  }
  return 0;
}


