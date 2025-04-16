#ifndef YYPARSER_H
#define YYPARSER_H

#include "ast/ast.h"
#include "ast/expressions.h"
#include "ast/functions.h"
#include "ast/statements.h"
#include "ast/types.h"
#include "utils/diagnostics.h"

#include <deque>
#include <variant>

int yylex();
extern int yydebug;
extern int yylineno;
extern Location yylloc;

extern int yyparse();
extern FILE *yyin;

extern AST yyast;

void yyerror(const Location &loc, const char *);

class SymbolStack {
  // We use a deque to store all values and we use nullptr to mark the limit
  // between frames. All values are sorted from last to be pushed to first
  // (this is done cheaply by deque push_front()) and thus searching should
  // be more or less efficient (we are traversing the addresses from low to
  // high).
public:
  struct FrameBoundary {};
  using type = std::variant<FrameBoundary, SymDec *, FunDef *>;

  // Represent the three states result: not found, found with matching case
  // and mach with different case.
  struct None {};
  STRONGTYPEDEF(type, Found);
  STRONGTYPEDEF(type, FoundWithDifferentCase);
  using Result = std::variant<None, Found, FoundWithDifferentCase>;

  template <typename T> void push(T value) { data_.push_front({value}); }

  void pushFrame() { data_.push_front(FrameBoundary{}); }

  void popFrame() {
    // While there is some values in the vector and the last one the boudary,
    // we remove the element of the last frame.
    while (data_.size() &&
           !std::holds_alternative<FrameBoundary>(data_.front())) {
      data_.pop_front();
    }
    data_.pop_front();
  }

  Result find_last_frame(std::string_view name) {
    for (auto it = begin(data_); it != end(data_); ++it) {
      // Detect the limit of frame and stop.
      if (std::holds_alternative<FrameBoundary>(*it)) {
        break;
      }

      if (!strcmp(get_name(*it), name.data())) {
        return Result(Found(*it));
      }
    }

    for (auto it = begin(data_); it != end(data_); ++it) {
      // Detect the limit of frame and stop.
      if (std::holds_alternative<FrameBoundary>(*it)) {
        break;
      }

      if (!strcasecmp(get_name(*it), name.data())) {
        return FoundWithDifferentCase(*it);
      }
    }
    return None();
  }

  Result find(std::string_view name) {
    for (auto it = begin(data_); it != end(data_); ++it) {
      // Detect the limit of frame and ingore it.
      if (std::holds_alternative<FrameBoundary>(*it)) {
        continue;
      }

      if (!strcmp(get_name(*it), name.data())) {
        return Found(*it);
      }
    }

    for (auto it = begin(data_); it != end(data_); ++it) {
      // Detect the limit of frame and ingore it.
      if (std::holds_alternative<FrameBoundary>(*it)) {
        continue;
      }
      if (!strcasecmp(get_name(*it), name.data())) {
        return FoundWithDifferentCase(*it);
      }
    }

    return None();
  }

#ifdef DEBUG
  void dump() {
    for (auto it = begin(data_); it != end(data_); ++it) {
      // frame limit
      if (std::holds_alternative<FrameBoundary>(*it)) {
        std::cerr << "======================================\n";
      } else {
        std::cerr << get_name(*it) << '\n';
      }
    }
  }
#endif

  const char *get_name(type v) {
    return std::visit(overloaded{[](SymDec *s) { return s->getname(); },
                                 [](FunDef *s) { return s->getname(); },
                                 [](FrameBoundary) {
                                   UNREACHABLE();
                                   return "";
                                 }},
                      v);
  }

  Location get_loc(type v) {
    return std::visit(overloaded{[](SymDec *s) { return s->loc(); },
                                 [](FunDef *s) { return s->loc(); },
                                 [](FrameBoundary) {
                                   UNREACHABLE();
                                   return Location::dummy();
                                 }},
                      v);
  }

private:
  std::deque<type> data_;
};

#endif // YYPARSER_H
