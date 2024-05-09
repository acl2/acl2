#include <iomanip>

#include "expressions.h"
#include "functions.h"
#include "statements.h"

//***********************************************************************************
// class Expression
//***********************************************************************************

Expression::Expression () { needsParens = false; }

bool
Expression::isSymRef ()
{
  return false;
} // virtual

bool
Expression::isConst ()
{
  return false;
} // virtual

// Value of expression, applicable to a limited variety of integer-valued
// constant expressions:

int
Expression::evalConst ()
{ // virtual (overridden by constant expressions)
  assert (!"attempt to evaluate a non-constant expression");
  return 0;
}

bool
Expression::isArray ()
{
  return false;
} // virtual

bool
Expression::isStruct ()
{
  return false;
} // virtual

bool
Expression::isNumber ()
{
  return !isArray () && !isStruct ();
}

bool
Expression::isSubrange ()
{
  return false;
} // virtual

bool
Expression::isInteger ()
{ // virtual
  return false;
}

bool
Expression::isFP ()
{
  return isNumber () && !isInteger ();
}

// The following expressions have associated types: variable, array, and struct
// references; function calls; cast expressions; applications of "~" to typed
// expressions; and applications of "&", "|", and "^" to typed expressions of
// the same type.  For all other expressions, exprType is undefined:

Type *
Expression::exprType ()
{ // virtual (overridden by SymRef, Funcall, ArrayRef, StructRef, PrefixExpr,
  // and BinaryExpr)
  // Dereferenced type of expression.
  return nullptr;
}

// displayNoParens is defined for each class of expressions and is called by
// the non-virtual display method, which inserts parentheses as required:

// virtual void displayNoParens(ostream& os) const = 0;

void
Expression::display (ostream &os) const
{
  if (needsParens)
    os << "(";
  displayNoParens (os);
  if (needsParens)
    os << ")";
}

// The following method substitutes each occurrence of a given variable with a
// given value:

Expression *
Expression::subst ([[maybe_unused]] SymRef *var,
                   [[maybe_unused]] Expression *val)
{ // virtual
  return this;
}

// The following method converts an expression to an S-expression.  The
// argument isBV is relevant only for a typed expression of a register type
// (see exprType above).  In this case, if isBV is true, then the resulting
// S-expression should represent the value of the bit vector contents of the
// register, and otherwise it should represent the value of that bit vector as
// interpreted according to the type. The argument isBV is set the following
// cases: (1) The expression is being assigned to a register of the same type;
// (2) The expression is being assigned to an integer register and the
// expression is an unsigned
//     integer register of width not exceeding that of the target;
// (3) The resulting S-expression is to be the first argument of bitn, bits,
// setbitn, or setbits. (4) The expression is an argument of a logical
// expression of a register type.

Sexpression *
Expression::ACL2Expr ([[maybe_unused]] bool isBV)
{ // virtual
  assert (!"Expression cannot be converted to an S-expression");
  return nullptr;
}

// The following method converts an expression to an Sexpression to be used as
// an array initialization. It returns the same value as ACL2Expr, except for
// an Initializer:

Sexpression *
Expression::ACL2ArrayExpr ()
{ // virtual (overridden by Initializer)
  return ACL2Expr ();
}

// Translate to an ACL2 assignment with this lvalue and the rvalue given as the
// argument:

Sexpression *
Expression::ACL2Assign ([[maybe_unused]] Sexpression *rval)
{ // virtual (overridden by valid lvalues)
  assert (!"Assigment can be made only to an expression of type SymRef, "
           "ArrayRef, StructRef, BitRef, or Subrange");
  return nullptr;
}

// If a numerical expression is known to have a non-negative value of bounded
// width, then return the bound; otherwise, return 0:

unsigned
Expression::ACL2ValWidth ()
{ // virtual (overridden by BitRef and Subrange)
  Type *t = exprType ();
  return t ? t->ACL2ValWidth () : 0;
}

// The remaining Expression methods are defined solely for the purpose of
// making ACL2ValWidth a little smarter by computing the width of a Subrange
// expression when the limits differ by a computable constant:

bool
Expression::isPlusConst ([[maybe_unused]] Expression *e)
{ // virtual (overridden by BinaryExpr)
  // Used only by Subrange::ACL2ValWidth
  // Applied to the upper limit of a Subrange expression to determine whether
  // it is it is a binary expression representing the sum of the lower limit
  // and a constant.
  return false;
}

bool
Expression::isEqual (Expression *e)
{ // virtual (overridden by PrefixExpr and BinaryExpr)
  // Is this expression known to be equal in value to e?
  // Used only by isPlusConst.
  return this == e;
}

bool
Expression::isEqualPrefix ([[maybe_unused]] const char *o,
                           [[maybe_unused]] Expression *e)
{ // virtual (overridden by PrefixExpr)
  // Is this a prefix expression with the given operator and argument?
  // Used only by isEqual.
  return false;
}

bool
Expression::isEqualBinary ([[maybe_unused]] const char *o,
                           [[maybe_unused]] Expression *e1,
                           [[maybe_unused]] Expression *e2)
{ // virtual (overridden by BinaryExpr)
  // Is this a binary expression with the given operator and arguments?
  // Used only by isEqual.
  return false;
}

bool
Expression::isEqualConst ([[maybe_unused]] Constant *c)
{ // virtual (overridden by Constant)
  // Is this a constant equal to a given constant?
  // Used only by isEqual.
  return false;
}

bool
Expression::isEqualSymRef ([[maybe_unused]] SymDec *s)
{ // virtual (overridden by SymRef)
  // Is this a reference to a given symbol?
  // Used only by isEqual.
  return false;
}

bool
Expression::isInitializer ()
{ // virtual (overridden by Initializer)
  return false;
}

int
Expression::getPlusConst ()
{ // virtual (overridden by BinaryExpr)
  // Called on a binary expression for which isPlusConst is true; returns the
  // value of the constant.
  return 0;
}

// class Constant : public Expression, public Symbol
// -------------------------------------------------

Constant::Constant (const char *n) : Expression (), Symbol (n) {}

Constant::Constant (int n) : Expression (), Symbol (n) {}

bool
Constant::isConst ()
{
  return true;
}

void
Constant::displayNoParens (ostream &os) const
{
  os << getname ();
}

Sexpression *
Constant::ACL2Expr ([[maybe_unused]] bool isBV)
{
  return this;
}

bool
Constant::isEqual (Expression *e)
{
  return e->isEqualConst (this);
}

bool
Constant::isEqualConst (Constant *c)
{
  return !strcmp (getname (), c->getname ());
}

// class Integer : public Constant
// -------------------------------

Integer::Integer (const char *n) : Constant (n) {}

Integer::Integer (int n) : Constant (n) {}

int
Integer::evalConst ()
{
  if (!strncmp (getname (), "0x", 2))
    {
      return strtol (getname () + 2, nullptr, 16);
    }
  else if (!strncmp (getname (), "-0x", 3))
    {
      return -strtol (getname () + 3, nullptr, 16);
    }
  else
    {
      return atoi (getname ());
    }
}

Sexpression *
Integer::ACL2Expr ([[maybe_unused]] bool isBV)
{
  if (!strncmp (getname (), "0x", 2))
    {
      std::string new_name (getname ());
      new_name[0] = '#';
      Symbol *result = new Symbol (std::move (new_name));
      return result;
    }
  else if (!strncmp (getname (), "-0x", 3))
    {
      std::string new_name (getname () + 1);
      new_name[0] = '#';
      Symbol *result = new Symbol (std::move (new_name));
      return new Plist ({ &s_minus, result });
    }
  else
    {
      return this;
    }
}

Integer i_0 ("0");
Integer i_1 ("1");
Integer i_2 ("2");

// class Boolean : public Constant
// -------------------------------
Boolean::Boolean (const char *n) : Constant (n) {}

int
Boolean::evalConst ()
{
  if (!strcmp (getname (), "true"))
    return 1;
  else if (!strcmp (getname (), "false"))
    return 0;
  else
    UNREACHABLE ();
}

Boolean b_true ("true");
Boolean b_false ("false");

Sexpression *
Boolean::ACL2Expr ([[maybe_unused]] bool isBV)
{
  if (!strcmp (getname (), "true"))
    return new Plist ({ &s_true });
  else if (!strcmp (getname (), "false"))
    return new Plist ({ &s_false });
  else
    cout << getname () << endl;
  UNREACHABLE ();
}

// class SymRef : public Expression
// ---------------------------------------------------------------

// Reference to declared symbol, which may be an enumeration constant or a
// variable

// Data member: SymDec *symDec;

SymRef::SymRef (SymDec *s) : Expression () { symDec = s; }

bool
SymRef::isSymRef ()
{
  return true;
}

Type *
SymRef::exprType ()
{
  return symDec->type->derefType ();
}

bool
SymRef::isConst ()
{
  return symDec->isConst ();
}

int
SymRef::evalConst ()
{
  if (isConst ())
    {
      return symDec->evalConst ();
    }
  else
    {
      assert (!"Attempt to evaluate a non-constant symbol reference.");
    }
}

bool
SymRef::isArray ()
{
  return exprType ()->isArrayType ();
}

bool
SymRef::isStruct ()
{
  return exprType ()->isStructType ();
}

bool
SymRef::isInteger ()
{
  return exprType ()->isIntegerType ();
}

void
SymRef::displayNoParens (ostream &os) const
{
  symDec->sym->display (os);
}

Expression *
SymRef::subst (SymRef *var, Expression *val)
{
  return (symDec == var->symDec) ? val : (Expression *)this;
}

Sexpression *
SymRef::ACL2Expr (bool isBV)
{
  Sexpression *s = symDec->ACL2SymExpr ();
  return isBV ? s : exprType ()->ACL2Eval (s);
}

Sexpression *
SymRef::ACL2Assign (Sexpression *rval)
{
  return new Plist ({ &s_assign, symDec->sym, rval });
}

bool
SymRef::isEqual (Expression *e)
{
  return e->isEqualSymRef (symDec);
}

bool
SymRef::isEqualSymRef (SymDec *s)
{
  return s == symDec;
}

// class FunCall : public Expression (function call)
// -------------------------------------------------

// Data members:  FunDef *func; List<Expression> *args;

FunCall::FunCall (FunDef *f, List<Expression> *a) : Expression ()
{
  func = f;
  args = a;
}

Type *
FunCall::exprType ()
{
  return func->returnType->derefType ();
}

bool
FunCall::isArray ()
{
  return exprType ()->isArrayType ();
}

bool
FunCall::isStruct ()
{
  return exprType ()->isStructType ();
}

bool
FunCall::isInteger ()
{
  return exprType ()->isIntegerType ();
}

void
FunCall::displayNoParens (ostream &os) const
{

  os << func->getname () << "(";
  bool is_first = true;
  for_each (args, [&] (Expression *e) {
    if (!is_first)
      os << ", ";
    e->display (os);
    is_first = false;
  });

  os << ")";
}

Expression *
FunCall::subst (SymRef *var, Expression *val)
{
  List<Expression> *ptr = args;
  List<Expression> *newArgs = nullptr;
  while (ptr)
    {
      Expression *expr = ptr->value->subst (var, val);
      if (newArgs)
        {
          newArgs->add (expr);
        }
      else
        {
          newArgs = new List<Expression> (expr);
        }
      ptr = ptr->next;
    }
  return new FunCall (func, newArgs);
}

Sexpression *
FunCall::ACL2Expr (bool isBV)
{
  Plist *result = new Plist ({ new Symbol (func->getname ()) });
  List<VarDec> *p = func->params;
  List<Expression> *a = args;
  while (a)
    {
      result->add (p->value->type->derefType ()->ACL2Assign (a->value));
      a = a->next;
      p = p->next;
    }
  return isBV ? result : exprType ()->ACL2Eval (result);
}

// class TempCall : public Expression (function template Data)
// -------------------------------------------------

// call members:  Symbol *instanceSym; List<Expression> *params;

TempCall::TempCall (Template *f, List<Expression> *a, List<Expression> *p)
    : FunCall (f, a)
{
  params = p;
  if (f->calls == nullptr)
    {
      f->calls = new List<TempCall> (this);
    }
  else
    {
      f->calls->add (this);
    }
}

void
TempCall::displayNoParens (ostream &os) const
{
  os << func->getname () << "<";
  List<Expression> *ptr = params;
  while (ptr)
    {
      ptr->value->display (os);
      if (ptr->next)
        os << ", ";
      ptr = ptr->next;
    }
  os << ">(";
  ptr = args;
  while (ptr)
    {
      ptr->value->display (os);
      if (ptr->next)
        os << ", ";
      ptr = ptr->next;
    }
  os << ")";
}

Expression *
TempCall::subst (SymRef *var, Expression *val)
{
  TempCall *result = (TempCall *)FunCall::subst (var, val);
  List<Expression> *ptr = params;
  List<Expression> *newParams = nullptr;
  while (ptr)
    {
      Expression *expr = ptr->value->subst (var, val);
      if (newParams)
        {
          newParams->add (expr);
        }
      else
        {
          newParams = new List<Expression> (expr);
        }
      ptr = ptr->next;
    }
  result->params = newParams;
  return result;
}

Sexpression *
TempCall::ACL2Expr (bool isBV)
{
  dynamic_cast<Template *> (func)->bindParams (params);
  Plist *result = dynamic_cast<Plist *> (FunCall::ACL2Expr (isBV));
  result->list->value = instanceSym;
  return result;
}

// class Initializer : public Expression (array initializer)
// ---------------------------------------------------------

// Data member:  List<Constant> *vals;

Initializer::Initializer (List<Constant> *v) : Expression () { vals = v; }

bool
Initializer::isInitializer ()
{
  return true;
}

void
Initializer::displayNoParens (ostream &os) const
{
  os << "{";
  List<Constant> *ptr = vals;
  while (ptr)
    {
      ptr->value->Symbol::display (os);
      if (ptr->next)
        os << ", ";
      ptr = ptr->next;
    }
  os << "}";
}

Sexpression *
Initializer::ACL2Expr ([[maybe_unused]] bool isBV)
{
  BigList<Sexpression> *result
      = new BigList<Sexpression> ((Sexpression *)(vals->value->ACL2Expr ()));
  List<Constant> *ptr = vals->next;
  while (ptr)
    {
      result->add ((Sexpression *)(ptr->value->ACL2Expr ()));
      ptr = ptr->next;
    }
  return Plist::FromList (result->front ());
}

Sexpression *
Initializer::ACL2ArrayExpr ()
{
  List<Sexpression> *entries = ((Plist *)(ACL2Expr ()))->list;
  Plist *p = new Plist ();
  unsigned i = 0;
  while (entries)
    {
      if (strcmp (((Constant *)(entries->value))->getname (), "0"))
        {
          p->add (new Cons (new Integer (i), entries->value));
        }
      i++;
      entries = entries->next;
    }
  if (p->list)
    {
      p = new Plist ({ &s_quote, p });
    }
  return p;
}

Sexpression *
Initializer::ACL2StructExpr (List<StructField> *fields)
{
  Sexpression *result = new Plist ();
  List<Constant> *ptr = vals;
  assert (vals->length () == fields->length ());
  while (fields)
    {
      result
          = new Plist ({ &s_as, new Plist ({ &s_quote, fields->value->sym }),
                         ptr->value->ACL2Expr (), result });
      ptr = ptr->next;
      fields = fields->next;
    }
  return result;
}

// class ArrayRef : public Expression
// ----------------------------------

// Data members:  Expression *array; Expression *index;

ArrayRef::ArrayRef (Expression *a, Expression *i) : Expression ()
{
  array = a;
  index = i;
}

Type *
ArrayRef::exprType ()
{
  return ((ArrayType *)(array->exprType ()))->getBaseType ();
}

bool
ArrayRef::isArray ()
{
  return exprType ()->isArrayType ();
}

bool
ArrayRef::isInteger ()
{
  return exprType ()->isIntegerType ();
}

void
ArrayRef::displayNoParens (ostream &os) const
{
  array->display (os);
  os << "[";
  index->display (os);
  os << "]";
}

Expression *
ArrayRef::subst (SymRef *var, Expression *val)
{
  Expression *newIndex = index->subst (var, val);
  return (newIndex == index) ? this : new ArrayRef (array, newIndex);
}

Sexpression *
ArrayRef::ACL2Expr (bool isBV)
{
  Sexpression *s;
  if (array->isSymRef () && ((SymRef *)array)->symDec->isROM ())
    {
      s = new Plist ({ &s_nth, index->ACL2Expr (),
                       new Plist ({ ((SymRef *)array)->symDec->sym }) });
    }
  else if (array->isSymRef () && ((SymRef *)array)->symDec->isGlobal ())
    {
      s = new Plist ({ &s_ag, index->ACL2Expr (),
                       new Plist ({ ((SymRef *)array)->symDec->sym }) });
    }
  else
    {
      s = new Plist ({ &s_ag, index->ACL2Expr (), array->ACL2Expr () });
    }
  return isBV ? s : exprType ()->ACL2Eval (s);
}

Sexpression *
ArrayRef::ACL2Assign (Sexpression *rval)
{
  return array->ACL2Assign (
      new Plist ({ &s_as, index->ACL2Expr (), rval, array->ACL2Expr () }));
}

// class ArrayParamRef : public ArrayRef
// -------------------------------------

ArrayParamRef::ArrayParamRef (Expression *a, Expression *i) : ArrayRef (a, i)
{
}

Expression *
ArrayParamRef::subst (SymRef *var, Expression *val)
{
  Expression *newIndex = index->subst (var, val);
  return (newIndex == index) ? this : new ArrayParamRef (array, newIndex);
}

void
ArrayParamRef::displayNoParens (ostream &os) const
{
  array->display (os);
  os << "[";
  index->display (os);
  os << "]";
}

// class StructRef : public Expression
// -----------------------------------

// Data members:  Expression *base; char *field;

StructRef::StructRef (Expression *s, char *f) : Expression ()
{
  base = s;
  field = f;
}

Type *
StructRef::exprType ()
{
  return ((StructType *)(base->exprType ()))
      ->fields->find (field)
      ->type->derefType ();
}

bool
StructRef::isArray ()
{
  return exprType ()->isArrayType ();
}

bool
StructRef::isInteger ()
{
  return exprType ()->isIntegerType ();
}

void
StructRef::displayNoParens (ostream &os) const
{
  base->display (os);
  os << "." << field;
}

Sexpression *
StructRef::ACL2Expr (bool isBV)
{
  Symbol *sym = ((StructType *)(base->exprType ()))->fields->find (field)->sym;
  Sexpression *s = new Plist (
      { &s_ag, new Plist ({ &s_quote, sym }), base->ACL2Expr () });
  return isBV ? s : exprType ()->ACL2Eval (s);
}

Sexpression *
StructRef::ACL2Assign (Sexpression *rval)
{
  Symbol *sym = ((StructType *)(base->exprType ()))->fields->find (field)->sym;
  return base->ACL2Assign (new Plist (
      { &s_as, new Plist ({ &s_quote, sym }), rval, base->ACL2Expr () }));
}

// class BitRef : public Expression
// --------------------------------

// Data members: Expression *base; Expression *index;

BitRef::BitRef (Expression *b, Expression *i) : Expression ()
{
  base = b;
  index = i;
}

bool
BitRef::isInteger ()
{
  return true;
}

void
BitRef::displayNoParens (ostream &os) const
{
  base->display (os);
  os << "[";
  index->display (os);
  os << "]";
}

Expression *
BitRef::subst (SymRef *var, Expression *val)
{
  Expression *newBase = base->subst (var, val);
  Expression *newIndex = index->subst (var, val);
  return (newBase == base && newIndex == index)
             ? this
             : new BitRef (newBase, newIndex);
}

Sexpression *
BitRef::ACL2Expr ([[maybe_unused]] bool isBV)
{
  Sexpression *b = base->ACL2Expr (true);
  Sexpression *i = index->ACL2Expr ();
  return new Plist ({ &s_bitn, b, i });
}

Sexpression *
BitRef::ACL2Assign (Sexpression *rval)
{
  Sexpression *b = base->ACL2Expr (true);
  Sexpression *i = index->ACL2Expr ();
  unsigned n = (((RegType *)(base->exprType ()))->width ())->evalConst ();
  Integer *s = new Integer (n);
  return base->ACL2Assign (new Plist ({ &s_setbitn, b, s, i, rval }));
}

unsigned
BitRef::ACL2ValWidth ()
{
  return 1;
}

// class Subrange : public Expression
// ----------------------------------

// Data members: Expression *base; Expression *high; Expression *low;

Subrange::Subrange (Expression *b, Expression *h, Expression *l)
    : Expression ()
{
  base = b;
  high = h;
  low = l;
  width = 0;
}

Subrange::Subrange (Expression *b, Expression *h, Expression *l, unsigned w)
    : Expression ()
{
  base = b;
  high = h;
  low = l;
  width = w;
}

bool
Subrange::isSubrange ()
{
  return true;
}

bool
Subrange::isInteger ()
{
  return true;
}

void
Subrange::displayNoParens (ostream &os) const
{
  base->display (os);
  os << "[";
  high->display (os);
  os << ":";
  low->display (os);
  os << "]";
}

Expression *
Subrange::subst (SymRef *var, Expression *val)
{
  Expression *newBase = base->subst (var, val);
  Expression *newHigh = high->subst (var, val);
  Expression *newLow = low->subst (var, val);
  return (newBase == base && newHigh == high && newLow == low)
             ? this
             : new Subrange (newBase, newHigh, newLow);
}

Sexpression *
Subrange::ACL2Expr ([[maybe_unused]] bool isBV)
{
  Sexpression *b = base->ACL2Expr (true);
  Sexpression *hi = high->ACL2Expr ();
  Sexpression *lo = low->ACL2Expr ();
  return new Plist ({ &s_bits, b, hi, lo });
}

Sexpression *
Subrange::ACL2Assign (Sexpression *rval)
{
  Sexpression *b = base->ACL2Expr (true);
  Sexpression *hi = high->ACL2Expr ();
  Sexpression *lo = low->ACL2Expr ();
  unsigned n = (((RegType *)(base->exprType ()))->width ())->evalConst ();
  Integer *s = new Integer (n);
  return base->ACL2Assign (new Plist ({ &s_setbits, b, s, hi, lo, rval }));
}

unsigned
Subrange::ACL2ValWidth ()
{
  if (high->isConst () && low->isConst ())
    {
      return high->evalConst () - low->evalConst () + 1;
    }
  else if (high->isPlusConst (low))
    {
      return high->getPlusConst () + 1;
    }
  else
    {
      return width;
    }
}

// class PrefixExpr : public Expression
// ------------------------------------

// Data members: Expression *expr; const char *op;

PrefixExpr::PrefixExpr (Expression *e, const char *o) : Expression ()
{
  expr = e;
  op = o;
}

bool
PrefixExpr::isConst ()
{
  return expr->isConst ();
}

int
PrefixExpr::evalConst ()
{
  int val = expr->evalConst ();
  if (!strcmp (op, "+"))
    {
      return val;
    }
  else if (!strcmp (op, "-"))
    {
      return -val;
    }
  else if (!strcmp (op, "~"))
    {
      return -1 - val;
    }
  else if (!strcmp (op, "!"))
    {
      return val ? 1 : 0;
    }
  else
    UNREACHABLE ();
}

bool
PrefixExpr::isInteger ()
{
  return expr->isInteger ();
}

void
PrefixExpr::displayNoParens (ostream &os) const
{
  os << op;
  expr->display (os);
}

Expression *
PrefixExpr::subst (SymRef *var, Expression *val)
{
  Expression *newExpr = expr->subst (var, val);
  return (newExpr == expr) ? this : new PrefixExpr (newExpr, op);
}

Type *
PrefixExpr::exprType ()
{
  if (!strcmp (op, "~"))
    {
      return expr->exprType ();
    }
  else
    {
      return nullptr;
    }
}

Sexpression *
PrefixExpr::ACL2Expr (bool isBV)
{
  Sexpression *s = expr->ACL2Expr ();
  if (!strcmp (op, "+"))
    {
      return s;
    }
  else if (!strcmp (op, "-"))
    {
      return new Plist ({ &s_minus, s });
    }
  else if (!strcmp (op, "!"))
    {
      return new Plist ({ &s_lognot1, s });
    }
  else if (!strcmp (op, "~"))
    {
      Type *t = exprType ();
      if (t)
        {
          Plist *bv = new Plist ({ &s_lognot, expr->ACL2Expr (true) });
          if (isBV && t->isRegType ())
            {
              unsigned w = (((RegType *)t)->width ())->evalConst ();
              return new Plist ({ &s_bits, bv, new Integer (w - 1), &i_0 });
            }
          else
            {
              return t->ACL2Eval (bv);
              //?? return bv;
            }
        }
      else
        {
          return new Plist ({ &s_lognot, s });
        }
    }
  else
    UNREACHABLE ();
}

bool
PrefixExpr::isEqual (Expression *e)
{
  return this == e || e->isEqualPrefix (op, expr);
}

bool
PrefixExpr::isEqualPrefix (const char *o, Expression *e)
{
  return !strcmp (o, op) && e->isEqual (expr);
}

// class CastExpr : public Expression
// ----------------------------------

// Data members: Expression *expr; Type *type;

CastExpr::CastExpr (Expression *e, Type *t) : Expression ()
{
  expr = e;
  type = t;
}

Type *
CastExpr::exprType ()
{
  return type;
}

bool
CastExpr::isConst ()
{
  return expr->isConst ();
}

int
CastExpr::evalConst ()
{
  return expr->evalConst ();
}

bool
CastExpr::isInteger ()
{
  return expr->isInteger ();
}

void
CastExpr::displayNoParens (ostream &os) const
{
  expr->display (os);
}

Expression *
CastExpr::subst (SymRef *var, Expression *val)
{
  Expression *newExpr = expr->subst (var, val);
  return (newExpr == expr) ? this : new CastExpr (newExpr, type);
}

Sexpression *
CastExpr::ACL2Expr ([[maybe_unused]] bool isBV)
{
  return expr->ACL2Expr ();
}

// class BinaryExpr : public Expression
// ------------------------------------

// Data members: Expression *expr1; Expression *expr2; const char *op;

BinaryExpr::BinaryExpr (Expression *e1, Expression *e2, const char *o)
    : Expression ()
{
  expr1 = e1;
  expr2 = e2;
  op = o;
}

bool
BinaryExpr::isConst ()
{
  return expr1->isConst () && expr2->isConst ();
}

int
BinaryExpr::evalConst ()
{
  int val1 = expr1->evalConst ();
  int val2 = expr2->evalConst ();
  if (!strcmp (op, "+"))
    return val1 + val2;
  if (!strcmp (op, "-"))
    return val1 - val2;
  if (!strcmp (op, "*"))
    return val1 * val2;
  if (!strcmp (op, "/"))
    return val1 / val2;
  if (!strcmp (op, "%"))
    return val1 % val2;
  if (!strcmp (op, "<<"))
    return val1 << val2;
  if (!strcmp (op, ">>"))
    return val1 >> val2;
  if (!strcmp (op, "&"))
    return val1 & val2;
  if (!strcmp (op, "^"))
    return val1 ^ val2;
  if (!strcmp (op, "|"))
    return val1 | val2;
  if (!strcmp (op, "<"))
    return val1 < val2;
  if (!strcmp (op, ">"))
    return val1 > val2;
  if (!strcmp (op, "<="))
    return val1 <= val2;
  if (!strcmp (op, ">="))
    return val1 >= val2;
  if (!strcmp (op, "=="))
    return val1 == val2;
  if (!strcmp (op, "!="))
    return val1 != val2;
  if (!strcmp (op, "&&"))
    return val1 && val2;
  if (!strcmp (op, "||"))
    return val1 || val2;
  UNREACHABLE ();
}

bool
BinaryExpr::isInteger ()
{
  return expr1->isInteger () && expr2->isInteger ();
}

void
BinaryExpr::displayNoParens (ostream &os) const
{
  expr1->display (os);
  os << " " << op << " ";
  expr2->display (os);
}

Expression *
BinaryExpr::subst (SymRef *var, Expression *val)
{
  Expression *newExpr1 = expr1->subst (var, val);
  Expression *newExpr2 = expr2->subst (var, val);
  return (newExpr1 == expr1 && newExpr2 == expr2)
             ? this
             : new BinaryExpr (newExpr1, newExpr2, op);
}

Type *
BinaryExpr::exprType ()
{
  Type *t1 = expr1->exprType ();
  Type *t2 = expr2->exprType ();
  if ((!strcmp (op, "&") || !strcmp (op, "|") || !strcmp (op, "^"))
      && (t1 == t2))
    {
      return t1;
    }
  else
    {
      return nullptr;
    }
}

Sexpression *
BinaryExpr::ACL2Expr (bool isBV)
{
  Symbol *ptr;
  Sexpression *sexpr1 = expr1->ACL2Expr ();
  Sexpression *sexpr2 = expr2->ACL2Expr ();
  if (expr1->isFP () && !strcmp (op, "<<"))
    {
      return new Plist (
          { &s_times, sexpr1, new Plist ({ &s_expt, &i_2, sexpr2 }) });
    }
  else if (expr1->isFP () && !strcmp (op, ">>"))
    {
      return new Plist (
          { &s_divide, sexpr1, new Plist ({ &s_expt, &i_2, sexpr2 }) });
    }
  if (!strcmp (op, "+"))
    ptr = &s_plus;
  else if (!strcmp (op, "-"))
    ptr = &s_minus;
  else if (!strcmp (op, "*"))
    ptr = &s_times;
  else if (!strcmp (op, "/"))
    return new Plist ({ &s_fl, new Plist ({ &s_slash, sexpr1, sexpr2 }) });
  else if (!strcmp (op, "%"))
    ptr = &s_rem;
  else if (!strcmp (op, "<<"))
    ptr = &s_ash;
  else if (!strcmp (op, ">>"))
    {
      ptr = &s_ash;
      sexpr2 = new Plist ({ &s_minus, sexpr2 });
    }
  else if (!strcmp (op, "&"))
    ptr = &s_logand;
  else if (!strcmp (op, "^"))
    ptr = &s_logxor;
  else if (!strcmp (op, "|"))
    ptr = &s_logior;
  else if (!strcmp (op, "<"))
    ptr = &s_logless;
  else if (!strcmp (op, ">"))
    ptr = &s_loggreater;
  else if (!strcmp (op, "<="))
    ptr = &s_logleq;
  else if (!strcmp (op, ">="))
    ptr = &s_loggeq;
  else if (!strcmp (op, "=="))
    ptr = &s_logeq;
  else if (!strcmp (op, "!="))
    ptr = &s_logneq;
  else if (!strcmp (op, "&&"))
    ptr = &s_logand1;
  else if (!strcmp (op, "||"))
    ptr = &s_logior1;
  else
    UNREACHABLE ();
  if (exprType ()
      && (ptr == &s_logand || ptr == &s_logior || ptr == &s_logxor))
    {
      Plist *bv = new Plist (
          { ptr, expr1->ACL2Expr (true), expr2->ACL2Expr (true) });
      return isBV ? bv : exprType ()->ACL2Eval (bv);
    }
  else
    {
      return new Plist ({ ptr, sexpr1, sexpr2 });
    }
}

bool
BinaryExpr::isEqual (Expression *e)
{
  return this == e || e->isEqualBinary (op, expr1, expr2);
}

bool
BinaryExpr::isEqualBinary (const char *o, Expression *e1, Expression *e2)
{
  return !strcmp (o, op) && e1->isEqual (expr1) && e2->isEqual (expr2);
}

bool
BinaryExpr::isPlusConst (Expression *e)
{
  return !strcmp (op, "+") && expr1->isEqual (e) && expr2->isConst ();
}

int
BinaryExpr::getPlusConst ()
{
  return expr2->evalConst ();
}

// class CondExpr : public Expression (conditional expression)
// -----------------------------------------------------------

// Data members:  Expression *expr1; Expression *expr2; Expression *test;

CondExpr::CondExpr (Expression *e1, Expression *e2, Expression *t)
    : Expression ()
{
  expr1 = e1;
  expr2 = e2;
  test = t;
}

bool
CondExpr::isInteger ()
{
  return expr1->isInteger () && expr2->isInteger ();
}

void
CondExpr::displayNoParens (ostream &os) const
{
  test->display (os);
  os << " ? ";
  expr1->display (os);
  os << " : ";
  expr2->display (os);
}

Expression *
CondExpr::subst (SymRef *var, Expression *val)
{
  Expression *newExpr1 = expr1->subst (var, val);
  Expression *newExpr2 = expr2->subst (var, val);
  Expression *newTest = test->subst (var, val);
  return (newExpr1 == expr1 && newExpr2 == expr2 && newTest == test)
             ? this
             : new CondExpr (newExpr1, newExpr2, newTest);
}

Sexpression *
CondExpr::ACL2Expr ([[maybe_unused]] bool isBV)
{
  return new Plist (
      { &s_if1, test->ACL2Expr (), expr1->ACL2Expr (), expr2->ACL2Expr () });
}

// class MultipleValue : public Expression
// ---------------------------------------

// Data members: MvType *type; Expression *expr[8];

MultipleValue::MultipleValue (MvType *t, List<Expression> *e)
    : Expression (), type (t)
{

  expr.reserve (8);
  for (unsigned i = 0; i < 8 && e; ++i)
    {
      expr.push_back (e->value);
      e = e->pop ();
    }

  assert (expr.size () >= 2
          && "It does not make sense to have a mv with 1 or 0 elem");
  assert (type->type.size () == expr.size ()
          && "We should have as many types as values");
}

void
MultipleValue::displayNoParens (ostream &os) const
{

  os << "<";
  bool first = true;
  for (const auto e : expr)
    {
      if (!first)
        {
          os << ", ";
        }
      e->display (os);
    }
  os << ">";
}

Expression *
MultipleValue::subst (SymRef *var, Expression *val)
{

  std::vector<Expression *> newExpr;
  newExpr.reserve (8);
  bool isNew = false;

  for (unsigned i = 0; i < expr.size (); ++i)
    {
      newExpr.push_back (expr[i]->subst (var, val));
      if (newExpr[i] != expr[i])
        {
          isNew = true;
        }
    }
  return isNew ? new MultipleValue (type, std::move (newExpr)) : this;
}

Sexpression *
MultipleValue::ACL2Expr ([[maybe_unused]] bool isBV)
{

  Plist *result = new Plist ({ &s_mv });

  for (unsigned i = 0; i < expr.size (); ++i)
    {
      result->add (type->type[i]->derefType ()->ACL2Assign (expr[i]));
    }
  return result;
}
