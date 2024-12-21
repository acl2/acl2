#ifndef ASSERTION_H
#define ASSERTION_H

#include "visitor.h"

// Bind each assertion to its parent function (needed to disply where the
// correct message when the assert fails).
class MarkAssertionAction final
    : public RecursiveASTVisitor<MarkAssertionAction> {
public:
  MarkAssertionAction(const DiagnosticHandler &) {}

  bool VisitFunDef(FunDef *f) {
    fn_ = f;
    return true;
  }

  bool VisitAssertion(Assertion *a) {
    assert(fn_);
    a->funDef = fn_;
    return true;
  }

private:
  FunDef *fn_ = nullptr;
};

#endif // ASSERTION_H
