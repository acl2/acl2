#include <stdio.h>
#include <stdlib.h>
#include <string>
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

int main(int argc, char **argv) {
  ++argv, --argc;  /* skip over program name */
  if (argc > 0) {
    string buf = argv[0];
    buf += ".i";
    yyin = fopen(buf.c_str(), "r");
    if (yyin == NULL) {
      printf("Failed to open file '%s'\n", buf.c_str());
    }
    else {
      yylineno = 1;
      yyparse();
      // Restore basename
      buf.pop_back();
      buf.pop_back();

      if (prog.isEmpty())
        puts("Warning: no function definitions found,"
             " maybe you forgot the `// RAC begin` guard");

      if (argc > 1) {
        if (!strcmp(argv[1], "-acl2")) {
          buf += ".ast.lsp";
          fout.open(buf.c_str());
          prog.display(fout, acl2);
          fout.close();
        }
        else if (!strcmp(argv[1], "-rac")) {
          buf += ".pc";
          fout.open(buf.c_str());
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
