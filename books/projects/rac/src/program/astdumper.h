#ifndef ASTDUMPER_H
#define ASTDUMPER_H

#include "process/visitor.h"

#include <iostream>
#include <set>
#include <vector>

// Display the AST as a dot graph (https://graphviz.org/). This is mainly use
// for debuging. The adress of the node is used as identifier.
class ASTDumperAction final : public RecursiveASTVisitor<ASTDumperAction> {
public:
  // With the constructor and destructor, we write the top scope of the
  // graph.
  ASTDumperAction() {
    std::cout << "digraph ast {\n";
    parents_.reserve(128);
  }

  ~ASTDumperAction() { std::cout << "}"; }

  // For each node, we want to track its parents. The node at the end of the
  // parents_ vector is the current node and the one before is the direct
  // parent.
  bool TraverseExpression(Expression *e);
  bool TraverseStatement(Statement *s);
  bool TraverseType(const Type *t);

// Edge declaration: ID -> ID;
#define APPLY(CLASS, PARENT) bool Visit##CLASS(CLASS *ptr);
#include "parser/ast/astnodes.def"
#undef APPLY
#define APPLY(CLASS, PARENT) bool Visit##CLASS(const CLASS *ptr);
#include "parser/ast/types.def"
#undef APPLY

private:
  using base_t = RecursiveASTVisitor;
  // We don't need type info, the adress is enough.
  std::vector<const void *> parents_;

  // Keep track of the already declared edges to avoid multiple edge between
  // the same nodes.
  // Since we define Visit* for all classes, most of the edges will be doubled:
  // take for example the node Integer: we will run first VisitInteger, then
  // VisitConstant and finaly, VisitInteger.
  std::set<std::pair<const void *, const void *>> edges_;
};

#endif // ASTDUMPER_H
