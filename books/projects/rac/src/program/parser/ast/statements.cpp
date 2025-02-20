#include "expressions.h"
#include "functions.h"
#include "statements.h"
#include "types.h"

#include <algorithm>
#include <iomanip>

//***********************************************************************************
// class Statement
//***********************************************************************************

// Derived classes:

//   SimpleStatement       (statement that does not include substatements)
//
//     VarDec              (variable declaration)
//       ConstDec          (constant declaration)
//     MulVarDec           (multiple variable declaration)
//     MulConstDec         (multiple constant declaration)
//
//     BreakStmt           (break -- may occur only within a switch)
//     ReturnStmt          (return)
//     Assertion           (assert)
//
//     Assignment          (=, ++, --, +=, etc.)
//     MultipleAssignment  (assignment of multiple function value)
//
//     NullStmt            (null statement)
//   Block                 (list of statements)
//   IfStmt                (if or if ... else)
//   ForStmt               (for)
//   SwitchStmt            (switch)

// This method is designed to handle if ... else if ... :

void Statement::displayAsRightBranch(
    std::ostream &os, unsigned indent) { // virtual (overridden by IfStmt)
  display(os, indent + 2);
}

// This method is designed to handle nested blocks:

void Statement::displayWithinBlock(
    std::ostream &os, unsigned indent) { // virtual (overridden by Block)
  display(os, indent);
}

// Turn into a block if not already one:

Block *Statement::blockify() { // virtual (overridden by Block)
  return new Block(loc_, this);
}

// Create a block consisting of s appended to this:

Block *Statement::blockify(Statement *s) { // virtual (overridden by Block)
  return new Block(loc_, this, s);
}

// class SimpleStatement : public Statement
// ----------------------------------------

void SimpleStatement::display(std::ostream &os, unsigned indent) {
  os << "\n";
  if (indent) {
    os << std::setw(indent) << " ";
  }
  displaySimple(os);
  os << ";";
}

// class SymDec (symbol declaration)
// ------------

// Derived classes: EnumConstDec, VarDec, and TempParamDec.

// Data members: Symbol* sym; Type *type; Expression *init; (init is optional)

SymDec::SymDec(NodesId id, Location loc, const char *n, Type *t, Expression *i)
    : SimpleStatement(id, loc), sym(new Symbol(n)), init(i), type_(t),
      original_type_(t) {}

void SymDec::displaySymDec(std::ostream &os) const {
  original_type_->displayVarType(os);
  os << " ";
  original_type_->displayVarName(getname(), os);
  if (init) {
    os << " = ";
    init->display(os);
  }
}

bool SymDec::isStaticallyEvaluable() {
  return false;
} // overridden by EnumConstDec and ConstDec

int SymDec::evalConst() {
  assert(init);
  return init->evalConst();
}


Sexpression *
SymDec::ACL2SymExpr() { // Sexpression for a reference to this symbol.
  assert(!"Undefined method: ACL2SymExpr");
  return nullptr;
}

// class EnumConstDec : public SymDec
// ----------------------------------

EnumConstDec::EnumConstDec(Location loc, const char *n, Expression *v)
    : SymDec(idOf(this), loc, n, &intType, v) {}

void EnumConstDec::display(std::ostream &os, unsigned) {
  os << getname();
  if (init) {
    os << "=";
    init->display(os);
  }
}

bool EnumConstDec::isStaticallyEvaluable() { return true; }

Sexpression *EnumConstDec::ACL2SymExpr() {
  return always_cast<const EnumType *>(get_type())->getEnumVal(sym);
}

// class VarDec : public SimpleStatement, public SymDec (variable declaration)
// ---------------------------------------------------------------------------

VarDec::VarDec(Location loc, const char *n, Type *t, Expression *i)
    : SymDec(idOf(this), loc, n, t, i) {}

VarDec::VarDec(NodesId id, Location loc, const char *n, Type *t, Expression *i)
    : SymDec(id, loc, n, t, i) {}

void VarDec::displaySimple(std::ostream &os) { displaySymDec(os); }

Sexpression *VarDec::ACL2Expr() {

  const Type *t = get_type();

//  if (init) {
//    val = t->get_default_initializer();
//  } else {
//    t->cast(init->ACL2Expr());
//  }

  Sexpression *val = nullptr;
  if (isa<const ArrayType *>(t)) {
    if (!init) {
      val = new Plist();
    } else if (isGlobal()) {
      val = new Plist({ &s_quote, init->ACL2Expr() });
    } else if (Initializer *i = dynamic_cast<Initializer *>(init)) {
      val = i->ACL2ArrayExpr();
    } else {
      val = init->ACL2Expr();
    }
  } else if (auto struct_type = dynamic_cast<const StructType *>(t)) {
    if (!init) {
      Initializer i(Location::dummy(), {});
      val = i.ACL2StructExpr(struct_type->fields());
    } else if (Initializer *i = dynamic_cast<Initializer *>(init)) {
      val = i->ACL2StructExpr(struct_type->fields());
    } else {
      val = init->ACL2Expr();
    }
  } else if (isa<const MvType *>(t)) {
    if (Initializer *i = dynamic_cast<Initializer *>(init)) {
      val = i->ACL2TupleExpr();
    } else {
      val = init->ACL2Expr();
    }
  } else {
    if (init) {
      val = t->cast(init);
    } else {
      val = Integer::zero_v(loc_)->ACL2Expr();
    }
  }
  return new Plist({ &s_declare, sym, val });
}

Sexpression *VarDec::ACL2SymExpr() {
  if (isGlobal()) {
    return new Plist({ sym });
  } else {
    return sym;
  }
}

// class MulVarDec : public SimpleStatement  (multiple variable declaration)
// ---------------------------------------------------------------------------

MulVarDec::MulVarDec(Location loc, VarDec *dec1, VarDec *dec2)
    : SimpleStatement(idOf(this), loc) {
  decs.push_back(dec1);
  decs.push_back(dec2);
}

MulVarDec::MulVarDec(Location loc, std::vector<VarDec *> &&d)
    : SimpleStatement(idOf(this), loc), decs(d) {}

Sexpression *MulVarDec::ACL2Expr() {
  Plist *result = new Plist({ &s_list });
  for (auto vd : decs) {
    result->add(vd->ACL2Expr());
  }
  return result;
}

// TODO refactore
void MulVarDec::displaySimple(std::ostream &os) {
  auto dlist = decs.begin();
  (*dlist)->get_type()->displayVarType(os);
  while (dlist != decs.end()) {
    os << " ";
    (*dlist)->get_type()->displayVarName((*dlist)->getname(), os);
    if ((*dlist)->init) {
      os << " = ";
      (*dlist)->init->display(os);
    }
    ++dlist;
    if (dlist != decs.end()) {
      os << ",";
    }
  }
}

// class MulConstDec : public SimpleStatement  (multiple constant declaration)
// ---------------------------------------------------------------------------

//MulConstDec::MulConstDec(Location loc, ConstDec *dec1, ConstDec *dec2)
//    : SimpleStatement(idOf(this), loc) {
//  decs.push_back(dec1);
//  decs.push_back(dec2);
//}
//
//MulConstDec::MulConstDec(Location loc, std::vector<ConstDec *> &&d)
//    : SimpleStatement(idOf(this), loc), decs(d) {}
//
//Sexpression *MulConstDec::ACL2Expr() {
//  Plist *result = new Plist({ &s_list });
//  for (auto d : decs) {
//    result->add(d->ACL2Expr());
//  }
//  return result;
//}
//
//// TODO refactore
//void MulConstDec::displaySimple(std::ostream &os) {
//  auto dlist = decs.begin();
//  (*dlist)->get_type()->displayVarType(os);
//  while (dlist != decs.end()) {
//    os << " ";
//    (*dlist)->get_type()->displayVarName((*dlist)->getname(), os);
//    if ((*dlist)->init) {
//      os << " = ";
//      (*dlist)->init->display(os);
//    }
//    ++dlist;
//    if (dlist != decs.end()) {
//      os << ",";
//    }
//  }
//}

// class TempParamDec : public VarDec  (template parameter declaration)
// --------------------------------------------------------------------

TempParamDec::TempParamDec(Location loc, const char *n, Type *t)
    : SymDec(idOf(this), loc, n, t) {}

bool TempParamDec::isStaticallyEvaluable() { return init; }

Sexpression *TempParamDec::ACL2SymExpr() {
  return init ? get_type()->cast(init) : sym;
}

// class BreakStmt : public SimpleStatement
// ----------------------------------------

BreakStmt::BreakStmt(Location loc) : SimpleStatement(idOf(this), loc) {}

void BreakStmt::displaySimple(std::ostream &os) { os << "break"; }

Sexpression *BreakStmt::ACL2Expr() { return &s_break; }

// class ReturnStmt : public SimpleStatement
// -----------------------------------------

// Data members: Expression *value;

ReturnStmt::ReturnStmt(Location loc, Expression *v)
    : SimpleStatement(idOf(this), loc), value(v) {}

void ReturnStmt::displaySimple(std::ostream &os) {
  os << "return ";
  value->display(os);
}

Sexpression *ReturnStmt::ACL2Expr() {
  return new Plist({ &s_return, returnType->cast(value) });
}

// class Assertion : public SimpleStatement
// ----------------------------------------

// Data member: Expression *expr;

Assertion::Assertion(Location loc, Expression *e)
    : SimpleStatement(idOf(this), loc), expr(e) {}

void Assertion::displaySimple(std::ostream &os) {
  os << "assert(";
  expr->display(os);
  os << ")";
}

Sexpression *Assertion::ACL2Expr() {
  assert(funDef && "MarkAssertion should be run first");
  return new Plist(
      { &s_assert, expr->ACL2Expr(), new Symbol(funDef->getname()) });
}

// class Assignment : public SimpleStatement
// -----------------------------------------

// Data members: Expression *lval; const char* op; Expression *rval;

Assignment::Assignment(Location loc, Expression *l, const char *o,
                       Expression *r)
    : SimpleStatement(idOf(this), loc), lval(l), op(o), rval(r) {}

void Assignment::displaySimple(std::ostream &os) {

  lval->display(os);

  if (!strcmp(op, "++") || !strcmp(op, "--")) {
    os << op;
  } else if (strcmp(op, "=")) {
    os << ' ' << op << ' ';
    always_cast<BinaryExpr *>(rval)->expr2->display(os);
  } else {
    os << ' ' << op << ' ';
    rval->display(os);
  }
}

Sexpression *Assignment::ACL2Expr() {
  Sexpression *sexpr = lval->get_type()->cast(rval);
  return lval->ACL2Assign(sexpr);
}

void Assignment::resolveOverload() {
  auto w = always_cast<const IntType *>(rval->get_type())->width();
  lval = new Subrange(loc_, lval, index, w);
  op = "=";
}

void Assignment::desugar() {

  if (!strcmp(op, "=") || !strcmp(op, "set_slc")) {
    // Do nothing.
    return;
  } else if (!strcmp(op, "++")) {
    rval = new BinaryExpr(loc_, lval, Integer::one_v(loc_),
                          BinaryExpr::Op::Plus);
  } else if (!strcmp(op, "--")) {
    rval = new BinaryExpr(loc_, lval, Integer::one_v(loc_),
                          BinaryExpr::Op::Minus);
  } else if (!strcmp(op, ">>=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::RShift);
  } else if (!strcmp(op, "<<=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::LShift);
  } else if (!strcmp(op, "+=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::Plus);
  } else if (!strcmp(op, "-=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::Minus);
  } else if (!strcmp(op, "*=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::Times);
  } else if (!strcmp(op, "/=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::Divide);
  } else if (!strcmp(op, "%=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::Mod);
  } else if (!strcmp(op, "&=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::BitAnd);
  } else if (!strcmp(op, "^=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::BitXor);
  } else if (!strcmp(op, "|=")) {
    rval = new BinaryExpr(loc_, lval, rval, BinaryExpr::Op::BitOr);
  } else {
    assert(!"Unknown assignment operator");
  }
}

// class MultipleAssignment : public SimpleStatement
// -------------------------------------------------

// Data members: Expression *lval[8]; FunCall *rval;

MultipleAssignment::MultipleAssignment(Location loc, FunCall *r,
                                       std::vector<Expression *> e)
    : SimpleStatement(idOf(this), loc), lval_(e), rval_(r) {}

void MultipleAssignment::displaySimple(std::ostream &os) {
  assert(lval_.size() > 0);
  os << "<";
  lval_[0]->display(os);
  for (Expression *e : lval_) {
    os << ", ";
    e->display(os);
  }
  os << "> = ";
  rval_->display(os);
}

// In the event that each target of a multiple assignment is a simple variable,
// the corrersponding S-expression  has the form

//   (MV-ASSIGN (var1 ... vark) fncall).

// Otherwise, for each target that is not a simple variable (i.e., a reference
// to an array entry, a struct field, a subrange, or a bit), a temporary
// variable and an additional assignment are introduced, and the S-expression
// has the form

//   (BLOCK (MV-ASSIGN (var1 ... vark) fncall) (ASSIGN ...) ... (ASSIGN ...)).

// For example, the statement

//   foo(...).assign(x, y[i], z.range(j, k))

// where y is an array and z is a register of width 8, generates the following:

//   (BLOCK (MV-ASSIGN (X TEMP-0 TEMP-1) (FOO ...))
//          (ASSIGN Y (AS I TEMP-0 Y))
//          (ASSIGN Z (SETBITS Z 8 J K TEMP-1))).

Sexpression *MultipleAssignment::ACL2Expr() {

  std::vector<Symbol *> tmp_vars;
  Plist *vars = new Plist();
  bool needs_tmp_vars = false;

  for (unsigned i = 0; i < lval_.size(); ++i) {

    if (SymRef *ref = dynamic_cast<SymRef *>(lval_[i])) {
      vars->add(ref->symDec->sym);
      tmp_vars.push_back(nullptr);
    } else {
      Symbol *s_temp = new Symbol("temp-" + std::to_string(i));
      vars->add(s_temp);
      tmp_vars.push_back(s_temp);
      needs_tmp_vars = true;
    }
  }

  Plist *mv_assign = new Plist({ &s_mv_assign, vars, rval_->ACL2Expr() });

  if (!needs_tmp_vars) {
    return mv_assign;
  }

  Plist *result_with_tmp = new Plist({ &s_block });

  for (int i = lval_.size() - 1; i >= 0; --i) {
    if (lval_[i]) {
      result_with_tmp->add(new Plist({ &s_declare, tmp_vars[i] }));
    }
  }

  result_with_tmp->add(mv_assign);

  for (unsigned i = 0; i < lval_.size(); ++i) {
    if (lval_[i]) {
      result_with_tmp->add(lval_[i]->ACL2Assign(tmp_vars[i]));
    }
  }

  return result_with_tmp;
}

// class NullStmt : public SimpleStatement (null statement)
// --------------------------------------------------

NullStmt::NullStmt(Location loc) : SimpleStatement(idOf(this), loc) {}

void NullStmt::displaySimple([[maybe_unused]] std::ostream &os) {}

Sexpression *NullStmt::ACL2Expr() { return new Plist({ &s_null }); }

// class Block : public Statement
// ------------------------------

Block::Block(Location loc, std::vector<Statement *> &&s)
    : Statement(idOf(this), loc), stmtList(s) {}

Block::Block(Location loc, Statement *s) : Statement(idOf(this), loc) {
  stmtList.push_back(s);
}

Block::Block(Location loc, Statement *s1, Statement *s2)
    : Statement(idOf(this), loc) {
  stmtList.push_back(s1);
  stmtList.push_back(s2);
}

Block *Block::blockify() { return this; }

Block *Block::blockify(Statement *s) {
  std::vector<Statement *> copy = stmtList;
  copy.push_back(s);
  return new Block(loc_, std::move(copy));
}

void Block::display(std::ostream &os, unsigned indent) {
  os << " {";
  if (stmtList.size()) {
    for (Statement *s : stmtList) {
      s->displayWithinBlock(os, indent);
    }
    os << "\n";
    if (indent > 2) {
      os << std::setw(indent - 2) << " ";
    }
  }
  os << "}";
}

void Block::displayWithinBlock(std::ostream &os, unsigned indent) {
  os << "\n" << std::setw(indent) << (indent ? " " : "") << "{";
  for (Statement *s : stmtList) {
    s->displayWithinBlock(os, indent + 2);
  }
  os << "\n";
  if (indent) {
    os << std::setw(indent) << " ";
  }
  os << "}";
}

Sexpression *Block::ACL2Expr() {
  Plist *result = new Plist({ &s_block });
  for (Statement *s : stmtList) {
    result->add(s->ACL2Expr());
  }
  return result;
}

// class IfStmt : public Statement
// -------------------------------

// Data members: Expression *test; Statement *left; Statement *right;

IfStmt::IfStmt(Location loc, Expression *t, Statement *l, Statement *r)
    : Statement(idOf(this), loc), test(t), left(l), right(r) {}

void IfStmt::display(std::ostream &os, unsigned indent) {
  os << "\n" << std::setw(indent) << " ";
  displayAsRightBranch(os, indent);
}

void IfStmt::displayAsRightBranch(std::ostream &os, unsigned indent) {
  os << "if (";
  test->display(os);
  os << ")";
  left->display(os, indent + 2);
  if (right) {
    os << "\n"
       << std::setw(indent) << " "
       << "else ";
    right->displayAsRightBranch(os, indent);
  }
}

Sexpression *IfStmt::ACL2Expr() {
  return new Plist({ &s_if, test->ACL2Expr(), left->blockify()->ACL2Expr(),
                     right ? right->blockify()->ACL2Expr() : new Plist() });
}

// class ForStmt : public Statement
// --------------------------------

// Data members: SimpleStatement *init; Expression *test; Assignment *update;
// Statement *body;

ForStmt::ForStmt(Location loc, SimpleStatement *v, Expression *t,
                 Assignment *u, Statement *b)
    : Statement(idOf(this), loc), init(v), test(t), update(u), body(b) {}

void ForStmt::display(std::ostream &os, unsigned indent) {
  os << "\n"
     << std::setw(indent) << " "
     << "for (";

  init->displaySimple(os);
  os << "; ";
  test->display(os);
  os << "; ";
  update->displaySimple(os);
  os << ")";
  body->display(os, indent + 2);
}

Sexpression *ForStmt::ACL2Expr() {
  Sexpression *sinit = init->ACL2Expr();
  Sexpression *stest = test->ACL2Expr();

  Sexpression *supdate = ((Plist *)(update->ACL2Expr()))->nth(2);
  return new Plist({ &s_for, new Plist({ sinit, stest, supdate }),
                     body->blockify()->ACL2Expr() });
}

// class Case : public Statement (component of switch statement)
// -------------------------------------------------------------

// Data members:   Expression *label; List<Statement> *action;

Case::Case(Location loc, Expression *l, std::vector<Statement *> &&a)
    : Statement(idOf(this), loc), label(l), action(a) {}

void Case::display(std::ostream &os, unsigned indent) {
  os << "\n" << std::setw(indent) << " ";
  if (label) {
    os << "case ";
    label->display(os);
  } else {
    os << "default";
  }
  os << ":";
  for (Statement *a : action) {
    a->displayWithinBlock(os, indent + 2);
  }
}

// class SwitchStmt : public Statement
// -----------------------------------

// Data members: Expression *test; List<Case> *cases;

SwitchStmt::SwitchStmt(Location loc, Expression *t, std::vector<Case *> c)
    : Statement(idOf(this), loc), test_(t), cases_(c) {}

void SwitchStmt::display(std::ostream &os, unsigned indent) {

  os << "\n"
     << std::setw(indent) << " "
     << "switch (";
  test_->display(os);
  os << ") {";

  std::for_each(cases_.begin(), cases_.end(),
                [&](Case *c) { c->display(os, indent); });

  os << "\n"
     << std::setw(indent) << " "
     << "}";
}

Sexpression *SwitchStmt::ACL2Expr() {

  Plist *result = new Plist({ &s_switch, test_->ACL2Expr() });

  std::vector<Sexpression *> labels;
  bool last_case_not_default = true;

  std::for_each(cases_.begin(), cases_.end(), [&](Case *c) {
    if (c->label) {
      labels.push_back(c->label->ACL2Expr());
      last_case_not_default = true;
    } else {
      last_case_not_default = false;
    }

    if (c->action.size()) {
      Sexpression *slabel = nullptr;
      if (labels.size() == 0) {
        slabel = &s_t;
      } else if (labels.size() == 1) {
        slabel = labels[0];
      } else {
        Plist *p = new Plist();
        for (auto s : labels) {
          p->add(s);
        }
        slabel = p;
      }

      Plist *s_case = new Plist({ slabel });

      for (Statement *a : c->action) {
        if (isa<BreakStmt *>(a)) {
          break;
        }
        s_case->add(a->ACL2Expr());
      }

      result->add(s_case);
      labels.clear();
    }
  });

  if (last_case_not_default) {
    result->add(new Plist({ &s_t }));
  }

  return result;
}
