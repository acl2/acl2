#include "statements.h"
#include "functions.h"

#include <iomanip>

//***********************************************************************************
// class Statement
//***********************************************************************************

// Derived classes:

//   SimpleStatement       (statement that does not include substatements)
//     VarDec              (variable declaration)
//       ConstDec          (constant declaration)
//     MulVarDec           (multiple variable declaration)
//     MulConstDec         (multiple constant declaration)
//     BreakStmt           (break -- may occur only within a switch)
//     ReturnStmt          (return)
//     Assertion           (assert)
//     Assignment          (=, ++, --, +=, etc.)
//     MultipleAssignment  (assignment of multiple function value)
//     NullStmt            (null statement)
//   Block                 (list of statements)
//   IfStmt                (if or if ... else)
//   ForStmt               (for)
//   SwitchStmt            (switch)

// This method is designed to handle if ... else if ... :

void
Statement::displayAsRightBranch (ostream &os, unsigned indent)
{ // virtual (overridden by IfStmt)
  display (os, indent + 2);
}

// This method is designed to handle nested blocks:

void
Statement::displayWithinBlock (ostream &os, unsigned indent)
{ // virtual (overridden by Block)
  display (os, indent);
}

// Turn into a block if not already one:

Block *
Statement::blockify ()
{ // virtual (overridden by Block)
  return new Block (this);
}

// Create a block consisting of s appended to this:

Block *
Statement::blockify (Statement *s)
{ // virtual (overridden by Block)
  return new Block (this, s);
}

// Substitute expr for each ocurrence of var in statement; var is assumed not
// to occur in the left side of any declaration or assignment:

Statement *
Statement::subst ([[maybe_unused]] SymRef *var,
                  [[maybe_unused]] Expression *expr)
{ // virtual
  return this;
}

// Translate to an S-expression for ACL2 translation:

// Sexpression *Statement::ACL2Expr() { // virtual
//  display(cout); cout << endl;
//  assert(!"Statement is not intended to be converted to an S-expression");
//  return nullptr;
//}

void
Statement::noteReturnType ([[maybe_unused]] Type *t)
{ // virtual (overridden by Block, ReturnStmt, and IfStmt)
}

void
Statement::markAssertions ([[maybe_unused]] FunDef *f)
{ // virtual (overridden by Assertion)
}

// class SimpleStatement : public Statement
// ----------------------------------------

SimpleStatement::SimpleStatement () : Statement () {}

void
SimpleStatement::display (ostream &os, unsigned indent)
{
  os << "\n";
  if (indent)
    {
      os << setw (indent) << " ";
    }
  displaySimple (os);
  os << ";";
}

// class EnumConstDec : public SymDec
// ----------------------------------

EnumConstDec::EnumConstDec (const char *n, Expression *v)
    : SymDec (n, &intType, v)
{
}

void
EnumConstDec::display (ostream &os) const
{
  os << getname ();
  if (init)
    {
      os << "=";
      init->display (os);
    }
}

bool
EnumConstDec::isConst ()
{
  return true;
}

Sexpression *
EnumConstDec::ACL2Expr ()
{
  if (init)
    {
      return new Plist ({ sym, init->ACL2Expr () });
    }
  else
    {
      return sym;
    }
}

Sexpression *
EnumConstDec::ACL2SymExpr ()
{
  return ((EnumType *)type)->getEnumVal (sym);
}



// class VarDec : public SimpleStatement, public SymDec (variable declaration)
// ---------------------------------------------------------------------------

VarDec::VarDec (const char *n, Type *t, Expression *i)
    : SimpleStatement (), SymDec (n, t, i)
{
}

void
VarDec::displaySimple (ostream &os)
{
  displaySymDec (os);
}

Statement *
VarDec::subst (SymRef *var, Expression *val)
{
  assert (var->symDec != this);
  if (init)
    {
      Expression *newInit = init->subst (var, val);
      return (init == newInit) ? this : new VarDec (getname (), type, newInit);
    }
  else
    {
      return this;
    }
}

Sexpression *
VarDec::ACL2Expr ()
{
  Sexpression *val;
  if (type->derefType ()->isArrayType ())
    {
      if (!init)
        {
          val = new Plist ();
        }
      else if (isROM ())
        {
          val = new Plist ({ &s_quote, init->ACL2Expr () });
        }
      else
        {
          val = init->ACL2ArrayExpr ();
        }
    }
  else if (type->derefType ()->isStructType ())
    {
      type = type->derefType ();
      if (!init)
        {
          val = new Plist ();
        }
      else if (init->isInitializer ())
        {
          val = ((Initializer *)init)
                    ->ACL2StructExpr (((StructType *)type)->fields);
        }
      else
        {
          val = init->ACL2ArrayExpr ();
        }
    }
  else if (init)
    {
      val = type->derefType ()->ACL2Assign (init);
    }
  else
    {
      val = &i_0;
    }
  return new Plist ({ &s_declare, sym, val });
}

Sexpression *
VarDec::ACL2SymExpr ()
{
  return sym;
}

// class ConstDec : public VarDec
// ------------------------------

ConstDec::ConstDec (const char *n, Type *t, Expression *i) : VarDec (n, t, i)
{
}

void
ConstDec::displaySimple (ostream &os)
{
  os << "const ";
  VarDec::displaySimple (os);
}

bool
ConstDec::isConst ()
{
  return type->isIntegerType ();
}

Statement *
ConstDec::subst ([[maybe_unused]] SymRef *var,
                 [[maybe_unused]] Expression *val)
{
  return this;
}

bool
ConstDec::isGlobal ()
{
  List<ConstDec> *decs = prog.constDecs;
  while (decs)
    {
      if (decs->value == this)
        return true;
      decs = decs->next;
    }
  return false;
}

bool
ConstDec::isROM ()
{
  return isGlobal () && type->isArrayType ();
}

Sexpression *
ConstDec::ACL2SymExpr ()
{
  if (isGlobal ())
    {
      return new Plist ({ sym });
    }
  else
    {
      return sym;
    }
}

// class MulVarDec : public SimpleStatement  (multiple variable declaration)
// ---------------------------------------------------------------------------

MulVarDec::MulVarDec (VarDec *dec1, VarDec *dec2) : SimpleStatement ()
{
  decs = new List<VarDec> (dec1, dec2);
}

MulVarDec::MulVarDec (List<VarDec> *d) : SimpleStatement () { decs = d; }

Statement *
MulVarDec::subst (SymRef *var, Expression *val)
{
  List<VarDec> *newDecs
      = new List<VarDec> ((VarDec *)(decs->value->subst (var, val)));
  List<VarDec> *d = decs->next;
  while (d)
    {
      newDecs->add ((VarDec *)(d->value->subst (var, val)));
      d = d->next;
    }
  return new MulVarDec (newDecs);
}

Sexpression *
MulVarDec::ACL2Expr ()
{
  Plist *result = new Plist ({ &s_list });
  List<VarDec> *ptr = decs;
  while (ptr)
    {
      result->add (ptr->value->ACL2Expr ());
      ptr = ptr->next;
    }
  return result;
}

void
MulVarDec::displaySimple (ostream &os)
{
  List<VarDec> *dlist = decs;
  VarDec *d = decs->value;
  d->type->displayVarType (os);
  while (dlist)
    {
      os << " ";
      d->type->displayVarName (d->getname (), os);
      if (d->init)
        {
          os << " = ";
          d->init->display (os);
        }
      dlist = dlist->next;
      if (dlist)
        {
          d = dlist->value;
          os << ",";
        }
    }
}

// class MulConstDec : public SimpleStatement  (multiple constant declaration)
// ---------------------------------------------------------------------------

MulConstDec::MulConstDec (ConstDec *dec1, ConstDec *dec2) : SimpleStatement ()
{
  decs = new List<ConstDec> (dec1, dec2);
}

MulConstDec::MulConstDec (List<ConstDec> *d) : SimpleStatement () { decs = d; }

Statement *
MulConstDec::subst (SymRef *var, Expression *val)
{
  List<ConstDec> *newDecs
      = new List<ConstDec> ((ConstDec *)(decs->value->subst (var, val)));
  List<ConstDec> *d = decs->next;
  while (d)
    {
      newDecs->add ((ConstDec *)(d->value->subst (var, val)));
      d = d->next;
    }
  return new MulConstDec (newDecs);
}

Sexpression *
MulConstDec::ACL2Expr ()
{
  Plist *result = new Plist ({ &s_list });
  List<ConstDec> *ptr = decs;
  while (ptr)
    {
      result->add (ptr->value->ACL2Expr ());
      ptr = ptr->next;
    }
  return result;
}

void
MulConstDec::displaySimple (ostream &os)
{
  List<ConstDec> *dlist = decs;
  ConstDec *d = decs->value;
  d->type->displayVarType (os);
  while (dlist)
    {
      os << " ";
      d->type->displayVarName (d->getname (), os);
      if (d->init)
        {
          os << " = ";
          d->init->display (os);
        }
      dlist = dlist->next;
      if (dlist)
        {
          d = dlist->value;
          os << ",";
        }
    }
}

// class TempParamDec : public VarDec  (template parameter declaration)
// --------------------------------------------------------------------

TempParamDec::TempParamDec (const char *n, Type *t) : SymDec (n, t)
{
  init = &i_1;
}

bool
TempParamDec::isConst ()
{
  return true;
}

Sexpression *
TempParamDec::ACL2SymExpr ()
{
  return init ? type->derefType ()->ACL2Assign (init) : &i_0;
}

// class BreakStmt : public SimpleStatement
// ----------------------------------------

BreakStmt::BreakStmt () : SimpleStatement () {}

void
BreakStmt::displaySimple (ostream &os)
{
  os << "break";
}

Sexpression *
BreakStmt::ACL2Expr ()
{
  return &s_break;
}

BreakStmt breakStmt;

// class ReturnStmt : public SimpleStatement
// -----------------------------------------

// Data members: Expression *value;

ReturnStmt::ReturnStmt (Expression *v) : SimpleStatement () { value = v; }

void
ReturnStmt::displaySimple (ostream &os)
{
  os << "return ";
  value->display (os);
}

Statement *
ReturnStmt::subst (SymRef *var, Expression *val)
{
  Expression *newValue = value->subst (var, val);
  return (value == newValue) ? this : new ReturnStmt (newValue);
}

Sexpression *
ReturnStmt::ACL2Expr ()
{
  return new Plist (
      { &s_return, returnType->derefType ()->ACL2Assign (value) });
}

void
ReturnStmt::noteReturnType (Type *t)
{
  returnType = t;
}

// class Assertion : public SimpleStatement
// ----------------------------------------

// Data member: Expression *expr;

Assertion::Assertion (Expression *e) : SimpleStatement () { expr = e; }

void
Assertion::displaySimple (ostream &os)
{
  os << "assert(";
  expr->display (os);
  os << ")";
}

Statement *
Assertion::subst (SymRef *var, Expression *val)
{
  Expression *newExpr = expr->subst (var, val);
  return (expr == newExpr) ? this : new Assertion (newExpr);
}

Sexpression *
Assertion::ACL2Expr ()
{
  return new Plist (
      { &s_assert, expr->ACL2Expr (), new Symbol (funDef->getname ()) });
}

void
Assertion::markAssertions (FunDef *f)
{
  funDef = f;
}
// class Assignment : public SimpleStatement
// -----------------------------------------

// Data members: Expression *lval; const char* op; Expression *rval;

Assignment::Assignment (Expression *l, const char *o, Expression *r)
    : SimpleStatement ()
{
  lval = l;
  op = o;
  rval = r;
}

void
Assignment::displaySimple (ostream &os)
{
  lval->display (os);
  if (rval)
    {
      os << " " << op << " ";
      rval->display (os);
    }
  else
    {
      os << op;
    }
}

Statement *
Assignment::subst (SymRef *var, Expression *val)
{
  Expression *newL = lval->subst (var, val);
  Expression *newR = rval ? rval->subst (var, val) : nullptr;
  return (lval == newL) && (rval == newR) ? this
                                          : new Assignment (newL, op, newR);
}

Sexpression *
Assignment::ACL2Expr ()
{
  Expression *expr = rval;
  if (!strcmp (op, "="))
    {
      expr = rval;
    }
  else if (!strcmp (op, "++"))
    {
      expr = new BinaryExpr (lval, &i_1, "+");
    }
  else if (!strcmp (op, "--"))
    {
      expr = new BinaryExpr (lval, &i_1, "-");
    }
  else if (!strcmp (op, ">>="))
    {
      expr = new BinaryExpr (lval, rval, ">>");
    }
  else if (!strcmp (op, "<<="))
    {
      expr = new BinaryExpr (lval, rval, "<<");
    }
  else if (!strcmp (op, "+="))
    {
      expr = new BinaryExpr (lval, rval, "+");
    }
  else if (!strcmp (op, "-="))
    {
      expr = new BinaryExpr (lval, rval, "-");
    }
  else if (!strcmp (op, "*="))
    {
      expr = new BinaryExpr (lval, rval, "*");
    }
  else if (!strcmp (op, "%="))
    {
      expr = new BinaryExpr (lval, rval, "%");
    }
  else if (!strcmp (op, "&="))
    {
      expr = new BinaryExpr (lval, rval, "&");
    }
  else if (!strcmp (op, "^="))
    {
      expr = new BinaryExpr (lval, rval, "^");
    }
  else if (!strcmp (op, "|="))
    {
      expr = new BinaryExpr (lval, rval, "|");
    }
  else
    {
      assert (!"Unknown assignment operator");
    }
  Type *t = lval->exprType ();
  Sexpression *sexpr = t ? t->ACL2Assign (expr) : expr->ACL2Expr ();
  return lval->ACL2Assign (sexpr);
}

// class AssignBit : public SimpleStatement (bit assignment)
// ---------------------------------------------------------

// Data members: Expression *base; Expression *index; Expression *val;

AssignBit::AssignBit (Expression *b, Expression *i, Expression *v)
    : SimpleStatement ()
{
  base = b, index = i;
  val = v;
}

void
AssignBit::displaySimple (ostream &os)
{
  base->display (os);
  os << ".assign_bit(";
  index->display (os);
  os << ", ";
  val->display (os);
  os << ")";
}

// class AssignRange : public SimpleStatement (subrange assignment)
// -----------------------------------------------------------------

// Data members: Expression *base; Expression *high; Expression *low;
// Expression *width; Expression *val;

AssignRange::AssignRange (Expression *b, Expression *h, Expression *l,
                          Expression *w, Expression *v)
    : SimpleStatement ()
{
  base = b, high = h;
  low = l;
  width = w;
  val = v;
}

void
AssignRange::displaySimple (ostream &os)
{
  base->display (os);
  os << ".assign_range<";
  high->display (os);
  os << ", ";
  low->display (os);
  if (width)
    {
      os << ", ";
      width->display (os);
    }
  os << ">(";
  val->displayNoParens (os);
  os << ")";
}

// class MultipleAssignment : public SimpleStatement
// -------------------------------------------------

// Data members: Expression *lval[8]; FunCall *rval;

MultipleAssignment::MultipleAssignment (FunCall *r,
                                        std::vector<Expression *> e)
    : SimpleStatement (), lval (e), rval (r)
{
}

void
MultipleAssignment::displaySimple (ostream &os)
{
  assert (lval.size () > 0);
  os << "<";
  lval[0]->display (os);
  for (Expression *e : lval)
    {
      os << ", ";
      e->display (os);
    }
  os << "> = ";
  rval->display (os);
}

Statement *
MultipleAssignment::subst (SymRef *var, Expression *val)
{

  Expression *newR = rval->subst (var, val);
  bool changed = (newR != rval);
  std::vector<Expression *> newL;

  for (Expression *e : lval)
    {

      Expression *temp = e->subst (var, val);
      if (temp != e)
        changed = true;

      newL.push_back (temp);
    }
  return changed ? new MultipleAssignment ((FunCall *)newR, newL) : this;
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

Sexpression *
MultipleAssignment::ACL2Expr ()
{
  Plist *vars = new Plist ();
  Plist *result = new Plist ({ &s_mv_assign, vars, rval->ACL2Expr () });
  bool isBlock = false;
  for (unsigned i = 0; i < lval.size(); i++)
    {
      if (lval[i]->isSymRef ())
        {
          vars->add (((SymRef *)lval[i])->symDec->sym);
        }
      else
        {
          if (!isBlock)
            {
              result = new Plist ({ result });
              isBlock = true;
            }

          Symbol *s_temp = new Symbol ("temp-" + std::to_string (i));
          vars->add (s_temp);
          result->add (lval[i]->ACL2Assign (s_temp));
          result->push (new Plist ({ &s_declare, s_temp }));
        }
    }
  if (isBlock)
    {
      result->push (&s_block);
    }
  return result;
}

// class NullStmt : public SimpleStatement (null statement)
// --------------------------------------------------

NullStmt::NullStmt () : SimpleStatement () {}

void
NullStmt::displaySimple ([[maybe_unused]] ostream &os)
{
}

Sexpression *
NullStmt::ACL2Expr ()
{
  return new Plist ({ &s_null });
}

NullStmt nullStmt;

// class Block : public Statement
// ------------------------------

// Data member: List<Statement> *stmtList;

Block::Block (List<Statement> *s) : Statement () { stmtList = s; }

Block::Block (Statement *s) : Statement ()
{
  stmtList = new List<Statement> (s);
}

Block::Block (Statement *s1, Statement *s2) : Statement ()
{
  stmtList = new List<Statement> (s1, new List<Statement> (s2));
}

Block::Block (Statement *s1, Statement *s2, Statement *s3) : Statement ()
{
  stmtList = new List<Statement> (
      s1, new List<Statement> (s2, new List<Statement> (s3)));
}

Block *
Block::blockify ()
{
  return this;
}

Block *
Block::blockify (Statement *s)
{
  return new Block (stmtList ? stmtList->copy ()->add (s)
                             : new List<Statement> (s));
}

void
Block::display (ostream &os, unsigned indent)
{
  os << " {";
  if (stmtList)
    {
      List<Statement> *ptr = stmtList;
      while (ptr)
        {
          ptr->value->displayWithinBlock (os, indent);
          ptr = ptr->next;
        }
      os << "\n";
      if (indent > 2)
        {
          os << setw (indent - 2) << " ";
        }
    }
  os << "}";
}

void
Block::displayWithinBlock (ostream &os, unsigned indent)
{
  os << "\n" << setw (indent) << (indent ? " " : "") << "{";
  List<Statement> *ptr = stmtList;
  while (ptr)
    {
      ptr->value->displayWithinBlock (os, indent + 2);
      ptr = ptr->next;
    }
  os << "\n";
  if (indent)
    {
      os << setw (indent) << " ";
    }
  os << "}";
}

Statement *
Block::subst (SymRef *var, Expression *val)
{
  List<Statement> *newList = nullptr;
  bool changed = false;
  for (int i = stmtList->length () - 1; i >= 0; i--)
    {
      List<Statement> *subList = stmtList->nthl (i);
      Statement *s = subList->value;
      Statement *sNew = s->subst (var, val);
      if (sNew != s)
        {
          changed = true;
        }
      if (changed)
        {
          newList = new List<Statement> (sNew, newList);
        }
      else
        {
          newList = subList;
        }
    }
  return changed ? new Block (newList) : this;
}

Sexpression *
Block::ACL2Expr ()
{
  Plist *result = new Plist ({ &s_block });
  List<Statement> *ptr = stmtList;
  while (ptr)
    {
      result->add (ptr->value->ACL2Expr ());
      ptr = ptr->next;
    }
  return result;
}

void
Block::noteReturnType (Type *t)
{
  List<Statement> *ptr = stmtList;
  while (ptr)
    {
      ptr->value->noteReturnType (t);
      ptr = ptr->next;
    }
}

void
Block::markAssertions (FunDef *f)
{
  List<Statement> *ptr = stmtList;
  while (ptr)
    {
      ptr->value->markAssertions (f);
      ptr = ptr->next;
    }
}

// class IfStmt : public Statement
// -------------------------------

// Data members: Expression *test; Statement *left; Statement *right;

IfStmt::IfStmt (Expression *t, Statement *l, Statement *r) : Statement ()
{
  test = t;
  left = l;
  right = r;
}

void
IfStmt::display (ostream &os, unsigned indent)
{
  os << "\n" << setw (indent) << " ";
  displayAsRightBranch (os, indent);
}

void
IfStmt::displayAsRightBranch (ostream &os, unsigned indent)
{
  os << "if (";
  test->display (os);
  os << ")";
  left->display (os, indent + 2);
  if (right)
    {
      os << "\n"
         << setw (indent) << " "
         << "else ";
      right->displayAsRightBranch (os, indent);
    }
}

Statement *
IfStmt::subst (SymRef *var, Expression *val)
{
  Expression *t = test->subst (var, val);
  Statement *l = left->subst (var, val);
  Statement *r = right ? right->subst (var, val) : nullptr;
  return (t == test && l == left && r == right) ? this : new IfStmt (t, l, r);
}

Sexpression *
IfStmt::ACL2Expr ()
{
  return new Plist (
      { &s_if, test->ACL2Expr (), left->blockify ()->ACL2Expr (),
        right ? right->blockify ()->ACL2Expr () : new Plist () });
}

void
IfStmt::noteReturnType (Type *t)
{
  left->noteReturnType (t);
  if (right)
    right->noteReturnType (t);
}

void
IfStmt::markAssertions (FunDef *f)
{
  left->markAssertions (f);
  if (right)
    right->markAssertions (f);
}

// class ForStmt : public Statement
// --------------------------------

// Data members: SimpleStatement *init; Expression *test; Assignment *update;
// Statement *body;

ForStmt::ForStmt (SimpleStatement *v, Expression *t, Assignment *u,
                  Statement *b)
    : Statement ()
{
  init = v;
  test = t;
  update = u;
  body = b;
}

void
ForStmt::display (ostream &os, unsigned indent)
{
  os << "\n"
     << setw (indent) << " "
     << "for (";
  init->displaySimple (os);
  os << "; ";
  test->display (os);
  os << "; ";
  update->displaySimple (os);
  os << ")";
  body->display (os, indent + 2);
}

Statement *
ForStmt::subst (SymRef *var, Expression *val)
{
  SimpleStatement *v = (SimpleStatement *)init->subst (var, val);
  Expression *t = test->subst (var, val);
  Assignment *u = (Assignment *)update->subst (var, val);
  Statement *b = body->subst (var, val);
  return (v == init && t == test && u == update && b == body)
             ? this
             : new ForStmt (v, t, u, b);
}

Sexpression *
ForStmt::ACL2Expr ()
{
  Sexpression *sinit = init->ACL2Expr ();
  Sexpression *stest = test->ACL2Expr ();
  Sexpression *supdate = ((Plist *)(update->ACL2Expr ()))->list->nth (2);
  return new Plist ({ &s_for, new Plist ({ sinit, stest, supdate }),
                      body->blockify ()->ACL2Expr () });
}

void
ForStmt::markAssertions (FunDef *f)
{
  body->markAssertions (f);
}

// class Case : public Statement (component of switch statement)
// -------------------------------------------------------------

// Data members:   Expression *label; List<Statement> *action;

Case::Case (Expression *l, List<Statement> *a)
{
  label = l;
  action = a;
}

void
Case::display (ostream &os, unsigned indent)
{
  os << "\n" << setw (indent) << " ";
  if (label)
    {
      os << "case ";
      label->display (os);
    }
  else
    {
      os << "default";
    }
  os << ":";
  List<Statement> *ptr = action;
  while (ptr)
    {
      ptr->value->displayWithinBlock (os, indent + 2);
      ptr = ptr->next;
    }
}

Case *
Case::subst (SymRef *var, Expression *val)
{
  List<Statement> *newAction = nullptr;
  bool changed = false;
  for (int i = action->length () - 1; i >= 0; i--)
    {
      List<Statement> *subList = action->nthl (i);
      Statement *s = subList->value;
      Statement *sNew = s->subst (var, val);
      if (sNew != s)
        {
          changed = true;
        }
      if (changed)
        {
          newAction = new List<Statement> (sNew, newAction);
        }
      else
        {
          newAction = subList;
        }
    }
  return changed ? new Case (label, newAction) : this;
}

void
Case::markAssertions (FunDef *f)
{
  List<Statement> *a = action;
  while (a)
    {
      a->value->markAssertions (f);
      a = a->next;
    }
}

// class SwitchStmt : public Statement
// -----------------------------------

// Data members: Expression *test; List<Case> *cases;

SwitchStmt::SwitchStmt (Expression *t, List<Case> *c)
    : Statement (), test (t), cases (BetterList<Case>::_from_raw (c))
{
}

void
SwitchStmt::display (ostream &os, unsigned indent)
{
  os << "\n"
     << setw (indent) << " "
     << "switch (";
  test->display (os);
  os << ") {";
  cases.displayList (os, indent);
  os << "\n"
     << setw (indent) << " "
     << "}";
}

Statement *
SwitchStmt::subst (SymRef *var, Expression *val)
{
  List<Case> *newCases = nullptr;
  bool changed = false;
  for (int i = cases.length () - 1; i >= 0; i--)
    {
      List<Case> *subList = cases.nthl (i);
      Case *c = subList->value;
      Case *cNew = c->subst (var, val);
      if (cNew != c)
        {
          changed = true;
        }
      if (changed)
        {
          newCases = new List<Case> (cNew, newCases);
        }
      else
        {
          newCases = subList;
        }
    }
  return changed ? new SwitchStmt (test, newCases) : this;
}

Sexpression *
SwitchStmt::ACL2Expr ()
{

  List<Sexpression> *result
      = new List<Sexpression> (&s_switch, test->ACL2Expr ());

  List<Case> *clist = cases._underlying ();
  List<Sexpression> *labels = nullptr;
  Expression *l;
  List<Statement> *a;
  List<Sexpression> *s;

  while (clist)
    {
      Case *c = clist->value;

      l = c->label;
      l = c->label;
      a = c->action;
      a = c->action;
      if (l)
        {
          labels = labels ? labels->add (l->ACL2Expr ())
                          : new List<Sexpression> (l->ACL2Expr ());
        }
      if (a)
        {
          Sexpression *slabel = !labels ? &s_t
                                        : !(labels->next)
                                              ? labels->value
                                              : Plist::FromList (labels);
          s = new List<Sexpression> (slabel);
          while (a && a->value != &breakStmt)
            {
              s->add (a->value->ACL2Expr ());
              a = a->next;
            }
          result->add (Plist::FromList (s));
          labels = nullptr;
        }

      clist = clist->next;
    }

  if (l)
    result->add (new Plist ({ &s_t }));

  return Plist::FromList (result);
}

void
SwitchStmt::markAssertions (FunDef *f)
{
  for_each (cases, [f] (Case *c) { c->markAssertions (f); });
}
