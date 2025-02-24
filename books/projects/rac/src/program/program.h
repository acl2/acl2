#ifndef PROGRAM_H
#define PROGRAM_H

#include "displaymode.h"
#include "parser/ast/ast.h"
#include "parser/utils/diagnostics.h"

#include <algorithm>
#include <string>
#include <vector>

//***********************************************************************************
// Programs
//***********************************************************************************

class Program : private AST {
public:
  // Apply all required passes (type check, desugarization, ...) to the
  // program.
  static std::optional<Program> process(AST &&ast, bool all_warnings);

  void dumpAsDot();

  // Display functions.
  void display(std::ostream &os, DispMode mode = DispMode::rac) const;

  // Run an action (implemented by v) on the full program in the following
  // order: types, constant declarations, template fuctions and functions.
  template <typename Visitor> bool runAction(Visitor *v) {
    return std::all_of(typeDefs_.begin(), typeDefs_.end(),
                       [&](auto e) { return v->TraverseType(e); }) &&
           std::all_of(globals_.begin(), globals_.end(),
                       [&](auto e) { return v->TraverseStatement(e); }) &&
           std::all_of(funDefs_.begin(), funDefs_.end(),
                       [&](auto e) { return v->TraverseStatement(e); });
  }

private:
  void displayGlobals(std::ostream &os, DispMode mode) const;
  void displayTypeDefs(std::ostream &os, DispMode mode) const;
  //  Templates are included in functions
  void displayFunDefs(std::ostream &os, DispMode mode) const;

  Program(AST ast) : AST(std::move(ast)) {}
};

#endif // PROGRAM_H
