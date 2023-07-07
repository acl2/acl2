* parser.yy, parser.ll: Fix bug where having RAC inside a comment was
  generating a token which is not used and was causing a syntax error. Remove
  lexer rule removing all tokens starting by Hector:: (instead use an #ifdef
  directive). When an multine comment is missing the `*/` at the end, exit with
  an error (TODO:improve the message).
* statements.h, output.c: Fix bug where using tie with more that 4 array access
  was causing an invalid read.
* rac.h: Add array and tupple (for now, limited to 6 elements) for compiler
  which does not support C++11 yet (can be the case with EDA tools).
* output.c: Fix regression where, in PC mode, the declaration was having
  a wrong semi-colon.

# bfe335137924e0956000b964d53c1ae94402855d (28/02/23)


## Short

* Move to C++17 and add testsuite, see tests/README.md for more details.
* Add error reporting when opening file (input and output).
* Better error reporting during parsing and add a new check for duplicate
  declaration.
* Now, if the certification fails, the `rac` script will report an error.

## Details

* everywhere: Upgrade to C++17, replace newstr by strdup, NULL by nullptr, add
  macro UNREACHABLE() and refactore. Add testsuite.
* main.c: Now check if every file open has not failed and add missing fclose.
* parser.h, output.c: MvType and MultipleValues are not limited to 8 elements.
  TODO: remove this limitation in the parser. Replace Stack by SymbolStack, a
  more efficient one, without using List. DispMode is now an enum class and not
  a C enum.
* paser.y: When an error which is not an syntax error (like some type error or
  redeclaration), abort the parsing and report an error. Not doing it was
  leading to some invalid reads. Enable `parse.lac full` to improve the error
  reporting, see Bison documentation for more details. Add new yyerror
  functions, for better, more precise, error messages (for now it uses fprintf
  as a quicke repacement for C++20 format, but this should be changed). Add new
  error for duplicate idenifier declaration.
* rac-skel: check if the certification has failed and report it.
