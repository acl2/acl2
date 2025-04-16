#include "parser.h"

#include "yyparser.h"

std::optional<AST> parse(const std::string &file, bool trace) {

  yyin = fopen(file.c_str(), "r");

  if (yyin == nullptr) {
    std::cerr << "Failed to open file " << file << ": " << strerror(errno)
              << '\n';
    return {};
  }

  yyast.diag().setup(yyin);

  yydebug = trace;
  yylineno = 1;
  yylloc = Location::from_file(file);
  if (yyparse())
    return {};

  if (yyast.isEmpty())
    puts("Warning: no function definitions found,"
         " maybe you forgot the `// RAC begin` guard");

  return {std::move(yyast)};
}
