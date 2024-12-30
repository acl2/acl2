15/11/23
========

* Add -pedantic option to enable extra checks for RAC constraints.
* Better assert handling, we don't need to undef assert by hand or by including
  rac.h.
* Fix casts.
* Add missing function/template call typing.
* Make version generation more robust.
* Add support for templated signed register.
* Add check for c-array passed as function parameter, only enable in pedantic
  mode.
* Better type dereference.
* Improve function/template location (they do not display their body anymore)
* Add constraint on template parameter (only in pedantic mode).
* Refactore and add documentation.

28/12/23
========

* Template parameter can now be used in ac_int and set_slc.
* Add tracing to the parser (used for debugging).
* Fix translation of integer division (now we use truncation instead of floor).
* Now every nodes are typed.
* Improve greatly error messages.
* Assinging a const variable now raise an error.
* Check the RAC restrictions, variables must be initialized and two variables
  share the same name with different cases, now it reports an error.
* Fix a bug in PrefixExpr::evalConst where the ! operator was doing a bool conversion
  instead of bool conversion AND not.
* Massive refactore and some bugs fixes.
* Add new option -dump-ast.
* Fix some regression in pseucode mode.
* MvType support any number of arguments
* Initialier list are more genreal.
* ac_fixed is deprecated.
* Add RAC_BYPASS_ERROR.
* Add divide assign operator (/=)

6/07/23
========

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

28/02/23
========

Short
-----

* Move to C++17 and add testsuite, see tests/README.md for more details.
* Add error reporting when opening file (input and output).
* Better error reporting during parsing and add a new check for duplicate
  declaration.
* Now, if the certification fails, the `rac` script will report an error.

Details
-------

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
  as a quick repacement for C++20 format, but this should be changed). Add new
  error for duplicate idenifier declaration.
* rac-skel: check if the certification has failed and report it.
