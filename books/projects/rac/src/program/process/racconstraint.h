#ifndef RACCONSTRAINT_H
#define RACCONSTRAINT_H

#include "visitor.h"

// Collection of small checks enable by -pedantic.
class RACConstraint final : public RecursiveASTVisitor<RACConstraint> {
public:
  RACConstraint(DiagnosticHandler &diag) : diag_(diag) {}

  // Check restriction on break:
  //   * default: statements... may occur only as the final case of the
  //     statement
  //   * case label: statements... break must always be the last statement
  //     except if there is no statement.
  //
  //   * break can only be used in a switch (they can't be used in a for loop).
  //
  // Check if variable are always initialized (reading a non initialized
  // variable is undefined behavior, so we forbid it).

  // Check if default is unique and the last case.
  bool VisitSwitchStmt(SwitchStmt *s);

  // Check if break is the last statement.
  bool TraverseCase(Case *s);
  bool VisitStatement(Statement *s);
  bool VisitBreakStmt(BreakStmt *s);

  // Check if variable are always initialized, VisitVarDec will also visit
  // ConstDecs. For the variable defined for the function parameter, disable
  // this check.
  bool TraverseFunDef(FunDef *f);
  bool TraverseTemplate(Template *f);
  bool VisitVarDec(VarDec *s);
  bool VisitMulVarDec(MulVarDec *s);

  // Check if no C array are passed as parameter (they can't be const).
  bool VisitFunDef(FunDef *fd);

  // Check if the template parameters are only primitive type values (the rest
  // is illegal or not supported).
  bool VisitTemplate(Template *f);

private:
  using base_t = RecursiveASTVisitor<RACConstraint>;

  DiagnosticHandler &diag_;

  std::optional<Location> previous_break_loc_ = {};
  Case *last_case_ = nullptr;
  bool in_switch_ = false;

  bool disable_assignement_check_ = false;
};

#endif // RACCONSTRAINT_H
