#include "racconstraint.h"
#include "returnfalse.h"

#include <optional>

bool RACConstraint::VisitSwitchStmt(SwitchStmt *s) {

  // Check that no case, other that the last one, is default.
  bool is_last = true;
  std::optional<Location> first_default_loc = {};

  for (auto it = s->cases().rbegin(); it != s->cases().rend(); ++it) {

    const auto &c = **it;

    if (c.isDefaultCase()) {
      if (!is_last) {

        if (first_default_loc) {

          diag_.new_error(c.loc(), "Duplicate default case")
              .context(s->loc())
              .note("previous default was declared here:")
              .note_location(*first_default_loc)
              .report();

        } else {
          diag_.new_error(c.loc(), "Default case is not the last case")
              .context(s->loc())
              .report();
        }

        return error();
      } else {
        first_default_loc = { c.loc() };
      }
    }

    is_last = false;
  }

  unsigned size = s->cases().size();
  assert(size); // s->cases() can never be empty (forbidden by the syntax)
  last_case_ = s->cases()[size - 1];

  return true;
}

bool RACConstraint::TraverseCase(Case *s) {

  in_switch_ = true;

  if (!base_t::TraverseCase(s)) {
    return error();
  }

  in_switch_ = false;

  if (s->action.size() && s != last_case_ && !previous_break_loc_) {
    diag_.new_error(s->loc(), "No break at the end of case").report();
    return error();
  }

  previous_break_loc_ = {};
  return true;
}

bool RACConstraint::VisitStatement(Statement *s) {

  if (previous_break_loc_) {
    diag_.new_error(s->loc(), "Statement after break")
        .note("this statment is hidden by")
        .note_location(*previous_break_loc_)
        .report();
    return error();
  }
  return true;
}

bool RACConstraint::VisitBreakStmt(BreakStmt *s) {

  if (!in_switch_) {
    diag_.new_error(s->loc(), "break outside of switch")
        .note("RAC forbid break and continue inside loops")
        .report();
    return error();
  }

  previous_break_loc_ = { s->loc() };
  return true;
}

bool RACConstraint::TraverseFunDef(FunDef *s) {
  // Copy and pasted from visitor.hxx.

  if (!postfixTraversal())
    if (!WalkUpFunDef(s))
      return error();

  disable_assignement_check_ = true;

  bool b = true;
  for (auto s : s->params()) {
    if (b && !TraverseStatement(s))
      b = false;
  }

  disable_assignement_check_ = false;

  if (!b)
    return error();

  if (!TraverseStatement(s->body()))
    return error();

  if (postfixTraversal())
    if (!WalkUpFunDef(s))
      return error();

  return true;
}

bool RACConstraint::TraverseTemplate(Template *s) {
  // Copy and pasted from visitor.hxx.

  if (!postfixTraversal())
    if (!WalkUpTemplate(s))
      return error();

  disable_assignement_check_ = true;

  bool b = true;
  for (auto s : s->params()) {
    if (b && !TraverseStatement(s))
      b = false;
  }

  disable_assignement_check_ = false;

  if (!b)
    return error();

  if (!TraverseStatement(s->body()))
    return error();

  if (postfixTraversal())
    if (!WalkUpTemplate(s))
      return error();

  return true;
}

bool RACConstraint::VisitVarDec(VarDec *s) {

  if (disable_assignement_check_) {
    return true;
  }

  if (!s->init) {
    diag_.new_error(s->loc(), "variable must be assigned directly")
        .note("non initialized variable can introduce undefined behavior")
        .report();
    return error();
  }
  return true;
}

bool RACConstraint::VisitMulVarDec(MulVarDec *s) {

  if (disable_assignement_check_) {
    return true;
  }

  bool sucess = true;
  for (auto vd : s->decs) {
    if (!vd->init) {
      diag_.new_error(vd->loc(), "variable must be assigned directly")
          .note("non initialized variable can introduce undefined behavior")
          .context(vd->loc())
          .report();
      sucess = false;
    }
  }

  if (!sucess)
    return error();
  else
    return true;
}

bool RACConstraint::VisitFunDef(FunDef *fd) {

  bool b = true;
  for (auto vd : fd->params()) {

    if (auto at = dynamic_cast<ArrayType *>(vd->get_type())) {
      if (!at->isSTDArray()) {

        auto orig = vd->get_original_type();

        std::stringstream ss;
        at->dim->display(ss);
        diag_
            .new_error(
                vd->loc(),
                format("Cannot pass a C array (`%s`) as function parameter",
                       orig->to_string().c_str()))
            .note(format("use array<%s, %s> instead",
                         at->baseType->to_string().c_str(),
                         ss.str().c_str()))
            .context(vd->loc())
            .report();
        b = false;
      }
    }
  }

  if (!b)
    return error();
  else
    return true;
}

bool RACConstraint::VisitTemplate(Template *f) {

  bool b = true;
  for (auto p : f->tempParams()) {
    if (!isa<PrimType *>(p->get_type())) {
      b = false;
      diag_
          .new_error(
              p->loc(),
              format("Illegal type `%s`, only primitive type (like int "
                     "or bool) value are allowed as template parameters.",
                     p->get_original_type()->to_string().c_str()))
          .report();
    }
  }

  if (!b)
    return error();
  else
    return true;
}
