#ifndef PARSER_H
#define PARSER_H

#include "ast/ast.h"

#include <optional>
#include <string>

// Parse the file given and return (maybe) its AST. This function is not thread
// safe.
std::optional<AST> parse(const std::string &file, bool trace);

#endif // PARSER_H
