#include "forconstraints.h"

#include "../parser/ast/types.h"

bool ForConstraints::TraverseForStmt(ForStmt *s) {

  // Travese init and recover the variable.
  init_block_ = true;

  if (!TraverseStatement(s->init))
    return false;

  if (!var_name_) {
    diag_.new_error(s->init->loc(), "No variable declared or assigned")
        .context(s->loc())
        .report();
    return false;
  }

  init_block_ = false;

  // Traverse the test expression and check if the variable is used.
  test_or_update_block_ = true;

  if (!TraverseExpression(s->test))
    return false;

  if (!found_) {
    diag_
        .new_error(s->test->loc(), format("The variable (%s) used in the "
                                          "recursive calls in never tested",
                                          var_name_))
        .context(s->loc())
        .report();
    return false;
  }
  found_ = false;

  // Traverse the update and check if the variable is assigned. This is not
  // perfect as we are looking for the use of "variable" and not really if it
  // assigned.
  if (!TraverseStatement(s->update))
    return false;

  if (!found_) {
    diag_
        .new_error(s->update->loc(), format("The variable (%s) used in the "
                                            "recursive calls in never updated",
                                            var_name_))
        .context(s->loc())
        .report();

    return false;
  }
  found_ = false;
  test_or_update_block_ = false;
  var_name_ = nullptr;

  return true;
}

bool ForConstraints::VisitVarDec(VarDec *s) {

  // If there is multiple variable declaration, only take the first one.
  if (init_block_ && !var_name_) {
    var_name_ = s->sym->getname();
  }
  return true;
}

bool ForConstraints::VisitSymRef(SymRef *s) {

  // If there is multiple variable declaration, only take the first one.
  if (init_block_ && !var_name_) {
    var_name_ = s->symDec->sym->getname();
    if (s->get_type()->ACL2ValWidth() != 32) {
      diag_
          .new_error(s->loc(), "Type width is not 32 (this is a bug and will "
                               "maybe one day fixed)")
          .note(format("Change the type os %s to int or uint", var_name_))
          .report();
      return false;
    }
  }

  if (test_or_update_block_) {
    if (!strcmp(s->symDec->sym->getname(), var_name_)) {
      found_ = true;
    }
  }

  return true;
}
