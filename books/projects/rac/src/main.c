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
        if (!strcmp(argv[1], "-ctos")) {
          strcat(buf, ".ctos.cpp");
          fout.open(buf);
          strcpy(buf, argv[0]);
          strcat(buf, "_sysc_t::");
          prog.CtoSDisplayConstDefs(fout, buf);
          prog.displayFunDefs(fout, ctos, buf);
          fout.close();
          strcpy(buf, argv[0]);
          strcat(buf, ".types.h");
          fout.open(buf);
          prog.displayTypeDefs(fout, ctos);
          fout.close();
          strcpy(buf, argv[0]);
          strcat(buf, ".decs.h");
          fout.open(buf);
          prog.displayConstDecs(fout, ctos);
          prog.displayFunDecs(fout);
          fout.close();
        }
        else if (!strcmp(argv[1], "-acl2")) {
          strcat(buf, ".ast.lisp");
          fout.open(buf);
          prog.display(fout, acl2);
          fout.close();
        }
        else if (!strcmp(argv[1], "-rac")) {
          strcat(buf, ".m");
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
    printf("  parse file -rac     convert to pure RAC syntax and write to file.m\n\n");
    printf("  parse file -ctos     generate CtoS-able code in file.ctos.cpp, file.types.h, and file.consts.h\n\n");
    printf("  parse file -acl2     write ACL2 translation to output.lisp\n\n");
    yyin = stdin;
  }
}
