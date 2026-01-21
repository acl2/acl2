#ifndef FORCONSTRAINTS_H
#define FORCONSTRAINTS_H

#include "visitor.h"

class ForConstraints final : public RecursiveASTVisitor<ForConstraints> {
public:
  ForConstraints(DiagnosticHandler &diag) : diag_(diag) {}

  // We check if the first variable defined in init (the variable that will be
  // used in the recurive calls) in updated and tested in the update and test
  // block.
  bool TraverseForStmt(ForStmt *);

  // To recover the variable, we are using VisitVarDec and VisitSymRef since
  // the variable can either be declare (either since or multiple, both are
  // covered by VisitVarDec) or assigned.
  //
  // To check if the variable is used in the test and update, we used
  // VisitSymRef. This is not enough to guarantee termination but it still
  // better that nothing.
  bool VisitVarDec(VarDec *s);
  bool VisitSymRef(SymRef *s);

private:
  using base_t = RecursiveASTVisitor<ForConstraints>;

  // The variables that will be used in the recursive calls.
  const char *var_name_ = nullptr;

  bool init_block_ = false;
  bool test_or_update_block_ = false;
  bool found_ = false;

  DiagnosticHandler &diag_;
};

#endif // FORCONSTRAINTS_H
