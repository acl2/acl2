#include <stdio.h>
#include <stdlib.h>
#include <iostream>
#include <fstream>
using namespace std;
#include "parser.h"
extern int  yyparse();
extern FILE *yyin;
extern FILE *yyout;
extern int yylineno;
extern Program prog;
ofstream fout;
char buf[80];

int main(int argc, char **argv) {
  ++argv, --argc;  /* skip over program name */
  if (argc > 0) {
    strcpy(buf, argv[0]);
    strcat(buf, ".i");
    yyin = fopen(buf, "r");
    if (yyin == NULL) {
      printf("Failed to open file '%s'\n", buf);
    }
    else {
      yylineno = 1;
      yyparse();
      if (argc > 1) {
        strcpy(buf, argv[0]);
        if (!strcmp(argv[1], "-acl2")) {
          strcat(buf, ".ast.lsp");
          fout.open(buf);
          prog.display(fout, acl2);
          fout.close();
        }
        else if (!strcmp(argv[1], "-rac")) {
          strcat(buf, ".pc");
          fout.open(buf);
          prog.display(fout, rac);
          fout.close();
        }
      }
    }
  }
  else {
    printf("Usage:\n");
    printf("  parse file           check that file.cpp is well formed\n");
    printf("  parse file -rac      convert to RAC pseudocode and write to file.pc\n\n");
    printf("  parse file -acl2     write ACL2 translation to output.lisp\n\n");
    yyin = stdin;
  }
}
