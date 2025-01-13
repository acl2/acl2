#include "astdumper.h"

#include "parser/ast/expressions.h"
#include "parser/ast/functions.h"
#include "parser/ast/statements.h"
#include "parser/ast/types.h"

bool ASTDumperAction::TraverseExpression(Expression *e) {
  parents_.push_back(e);
  bool b = base_t::TraverseExpression(e);
  parents_.pop_back();
  return b;
}

bool ASTDumperAction::TraverseStatement(Statement *s) {
  parents_.push_back(s);
  bool b = base_t::TraverseStatement(s);
  parents_.pop_back();
  return b;
}

bool ASTDumperAction::TraverseType(Type *t) {
  parents_.push_back(t);
  bool b = base_t::TraverseType(t);
  parents_.pop_back();
  return b;
}

#define APPLY(CLASS, PARENT)                                                  \
  bool ASTDumperAction::Visit##CLASS(CLASS *ptr) {                            \
                                                                              \
    /*  Node declaration: node_ADDRESS [label="KIND\nVALUE", shape=s]; */     \
    constexpr bool is_expression = std::is_base_of_v<Expression, CLASS>;      \
    const char *s = is_expression ? "diamond" : "oval";                       \
    std::cout << "node_" << ptr << " [label=\"" #CLASS;                       \
                                                                              \
    /* If it is an expression, show its type */                               \
    if constexpr (is_expression) {                                            \
      Expression *e = reinterpret_cast<Expression *>(ptr);                    \
      if (const Type *t = e->get_type()) {                                    \
        std::cout << '\n';                                                    \
        t->displayVarType();                                                  \
        std::cout << '(' << ')';                                              \
      }                                                                       \
    }                                                                         \
                                                                              \
    /* If it is an symbol declaration, show its type */                       \
    if constexpr (std::is_base_of_v<SymDec, CLASS>) {                         \
      SymDec *s = reinterpret_cast<SymDec *>(ptr);                            \
      std::cout << '\n'                                                       \
                << s->sym->getname() << ": " << s->get_type()->to_string();   \
    }                                                                         \
                                                                              \
    std::cout << "\", shape=" << s << "];\n";                                 \
                                                                              \
    /* If it is a symRef add a dotted edge to declaration of the symbol */    \
    if constexpr (std::is_same_v<SymRef, CLASS>) {                            \
      SymRef *r = reinterpret_cast<SymRef *>(ptr);                            \
      if (edges_.insert({ ptr, r }).second) {                                 \
        std::cout << "node_" << r << " -> "                                   \
                  << "node_" << r->symDec                                     \
                  << " [style=dotted, constraint=false];\n";                  \
      }                                                                       \
    }                                                                         \
                                                                              \
    if (parents_.size() >= 2) {                                               \
      void *p = parents_[parents_.size() - 2];                                \
                                                                              \
      if (edges_.insert({ p, ptr }).second) {                                 \
                                                                              \
        std::cout << "node_" << p << " -> "                                   \
                  << "node_" << ptr << ";\n";                                 \
      }                                                                       \
    }                                                                         \
    return true;                                                              \
  }
#include "parser/ast/astnodes.def"
#include "parser/ast/types.def"
#undef APPLY
