#include "program.h"

#include "astdumper.h"

#include "process/assertion.h"
#include "process/forconstraints.h"
#include "process/racconstraint.h"
#include "process/returnfalse.h"
#include "process/typing.h"

#include <algorithm>

std::optional<Program> Program::process(AST &&ast, bool all_warnings) {

  Program processed_ast(std::move(ast));

#define RUNPASS(ACTION)                                                       \
  {                                                                           \
    ACTION a(processed_ast.diag_);                                            \
    if (!processed_ast.runAction(&a) && !bypass_errors()) {                   \
      return {};                                                              \
    }                                                                         \
  }

  RUNPASS(TypingAction);

  if (all_warnings) {
    RUNPASS(RACConstraint);
    RUNPASS(ForConstraints);
  }

  RUNPASS(MarkAssertionAction);

  return { std::move(processed_ast) };
}

void Program::dumpAsDot() {
  ASTDumperAction a;
  runAction(&a);
}

void Program::displayTypeDefs(std::ostream &os, DispMode mode) const {
  // Note that type definitions are used in generating S-expressions for
  // constant declarations and function definitions, but are not represented
  // explicitly in the ACL2 translation.
  if (mode == DispMode::rac)
    std::for_each(typeDefs_.begin(), typeDefs_.end(),
                  [&os](auto v) { v->displayDef(os); });
}

void Program::displayGlobals(std::ostream &os, DispMode mode) const {
  if (mode == DispMode::rac)
    std::for_each(globals_.begin(), globals_.end(),
                  [&os](auto v) { v->display(os); });
  else
    std::for_each(globals_.begin(), globals_.end(),
                  [&os](auto v) { v->ACL2Expr()->display(os); });
}

void Program::displayFunDefs(std::ostream &os, DispMode mode) const {
  if (mode == DispMode::rac)
    std::for_each(funDefs_.begin(), funDefs_.end(),
                  [&os](auto v) { v->display(os, 0); });
  else
    std::for_each(funDefs_.begin(), funDefs_.end(),
                  [&os](auto v) { v->ACL2Expr()->display(os); });
}

void Program::display(std::ostream &os, DispMode mode) const {
  displayTypeDefs(os, mode);
  os << '\n';
  displayGlobals(os, mode);
  os << '\n';
  displayFunDefs(os, mode);
  os << '\n';
}
