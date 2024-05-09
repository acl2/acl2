#include "types.h"
#include "expressions.h"
#include "statements.h"

#include <iomanip>

//***********************************************************************************
// class Type
//***********************************************************************************

Sexpression *
Type::ACL2Assign (Expression *rval)
{ // virtual (overridden by RegType)
  // Convert rval to an S-expression to be assigned to an object of this type.
  return rval->ACL2Expr ();
}

// class PrimType : public Symbol, public Type (Primitive type)
// ------------------------------------------------------------

PrimType boolType ("bool");
PrimType intType ("int");
PrimType uintType ("uint");
PrimType int64Type ("int64", "int");
PrimType uint64Type ("uint64", "uint");

// class RegType : public Type (Algorithmic C register type)
// ---------------------------------------------------

// Data member:  Expression *width

// bool RegType::isRegType() {return true;}
//
// bool RegType::isSigned() {return false;} // virtual

Sexpression *
RegType::ACL2Assign (Expression *rval)
{ // overridden by FPType

  Type *t = rval->exprType ();
  unsigned w = rval->ACL2ValWidth ();

  int width_evaluated = width_->evalConst ();
  assert (width_evaluated >= 0);

  if (t == this || (w && w <= (unsigned)width_evaluated))
    {
//      UNREACHABLE();
      return rval->ACL2Expr (true);
    }
  else
    {
      assert(width_evaluated);
      Sexpression *s = rval->ACL2Expr ();
      if (rval->isFP ())
        s = new Plist ({ &s_fl, s });
      return new Plist (
          { &s_bits, s, new Integer (width_->evalConst () - 1), &i_0 });
    }
}

// class UintType : public RegType
// -------------------------------

void
UintType::display (ostream &os) const
{
  os << "sc_uint<";
  width ()->displayNoParens (os);
  os << ">";
}

unsigned
UintType::ACL2ValWidth ()
{
  return width ()->evalConst ();
}

// class IntType : public RegType
// ------------------------------

void
IntType::display (ostream &os) const
{
  os << "sc_int<";
  width ()->displayNoParens (os);
  os << ">";
}

Sexpression *
IntType::ACL2Eval (Sexpression *s)
{
  return new Plist ({ &s_si, s, new Integer (width ()->evalConst ()) });
}

// class FPType :public RegType
// ----------------------------

// Data member:  Expression *iwidth

FPType::FPType (Expression *w, Expression *iw) : RegType (w) { iwidth = iw; }

Sexpression *
FPType::ACL2Assign (Expression *rval)
{
  Type *t = rval->exprType ();
  // ??? should be *this == *t sauf que vu que c'est des ptr partout ca
  // marchera pas...
  if (t == this)
    {
      return rval->ACL2Expr (true);
    }
  else
    {
      Sexpression *s = rval->ACL2Expr ();
      int wVal = width ()->evalConst (), iwVal = iwidth->evalConst ();
      s = new Plist (
          { &s_times, s,
            new Plist ({ &s_expt, &i_2, new Integer (wVal - iwVal) }) });
      if ((rval->isFP ()) || wVal < iwVal)
        s = new Plist ({ &s_fl, s });
      return new Plist ({ &s_bits, s, new Integer (wVal - 1), &i_0 });
    }
}

// class UfixedType : public FPType
// ---------------------------------

UfixedType::UfixedType (Expression *w, Expression *iw) : FPType (w, iw) {}

void
UfixedType::display (ostream &os) const
{
  os << "sc_ufixed<";
  width ()->displayNoParens (os);
  os << ", ";
  iwidth->displayNoParens (os);
  os << ">";
}

Sexpression *
UfixedType::ACL2Eval (Sexpression *s)
{
  return new Plist ({ &s_divide, s,
                      new Plist ({ &s_expt, &i_2,
                                   new Integer (width ()->evalConst ()
                                                - iwidth->evalConst ()) }) });
}

// class FixedType : public RegType
// --------------------------------

FixedType::FixedType (Expression *w, Expression *iw) : FPType (w, iw) {}

bool
FixedType::isSigned ()
{
  return true;
}

void
FixedType::display (ostream &os) const
{
  os << "sc_fixed<";
  width ()->displayNoParens (os);
  os << ", ";
  iwidth->displayNoParens (os);
  os << '>';
}

Sexpression *
FixedType::ACL2Eval (Sexpression *s)
{
  Sexpression *numerator
      = new Plist ({ &s_si, s, new Integer (width ()->evalConst ()) });
  Sexpression *denominator = new Plist (
      { &s_expt, &i_2,
        new Integer (width ()->evalConst () - iwidth->evalConst ()) });
  return new Plist ({ &s_divide, numerator, denominator });
}

// class ArrayType : public Type
// -----------------------------

// Data members: Type *baseType; Expresion *dim;

Type *
ArrayType::getBaseType ()
{
  return baseType->derefType ();
}

void
ArrayType::display (ostream &os) const
{
  baseType->display (os);
  os << "[";
  dim->displayNoParens (os);
  os << "]";
}

void
ArrayType::displayVarType (ostream &os) const
{
  baseType->display (os);
}

void
ArrayType::displayVarName (const char *name, ostream &os) const
{
  os << name << '[';
  dim->displayNoParens (os);
  os << ']';
}

void
ArrayType::makeDef (const char *name, ostream &os)
{
  Type *b = baseType;
  List<Expression> *dims = new List<Expression> (dim);
  while (b->isArrayType ())
    {
      dims = dims->push (((ArrayType *)b)->dim);
      b = ((ArrayType *)b)->baseType;
    }
  os << "\ntypedef ";
  b->display (os);
  os << " " << name;
  while (dims)
    {
      os << "[";
      (dims->value)->displayNoParens (os);
      os << "]";
      dims = dims->next;
    }
  os << ";";
}

// class StructField
// -----------------

// Data members:  Symbol *sym; Type *type;

StructField::StructField (Type *t, char *n)
{
  sym = new Symbol (n);
  type = t;
}

void
StructField::display (ostream &os, unsigned indent) const
{
  if (indent)
    {
      os << setw (indent) << " ";
    }
  type->display (os);
  os << " " << getname () << ";";
}

// class StructType : public Type
// ------------------------------

// Data member:  List<StructField> *fields;

StructType::StructType (List<StructField> *f) { fields = f; }

void
StructType::displayFields (ostream &os) const
{
  os << "{";
  List<StructField> *ptr = fields;
  while (ptr)
    {
      ptr->value->display (os);
      if (ptr->next)
        os << " ";
      ptr = ptr->next;
    }
  os << "}";
}

void
StructType::display (ostream &os) const
{
  os << "struct ";
  this->displayFields (os);
}

void
StructType::makeDef (const char *name, ostream &os)
{
  os << "\nstruct " << name << " ";
  displayFields (os);
  os << ";";
}

// class EnumType : public Type
// ----------------------------

// Data member:  List<EnumConstDec> *vals;

EnumType::EnumType (List<EnumConstDec> *v)
{
  vals = v;
  for_each (vals, [this] (EnumConstDec *e) { e->type = this; });
}

Sexpression *
EnumType::ACL2Expr ()
{
  Plist *result = new Plist ();
  for_each (vals, [this, result] (EnumConstDec *e) {
    result->add (e->ACL2Expr ());
  });
  return result;
}

void
EnumType::displayConsts (ostream &os) const
{
  os << "{";
  bool is_first = true;
  for_each (vals, [&] (EnumConstDec *e) {
    if (!is_first)
      os << ", ";
    e->display (os);
    is_first = false;
  });
  os << "}";
}

void
EnumType::display (ostream &os) const
{
  os << "enum ";
  displayConsts (os);
}

Sexpression *
EnumType::getEnumVal (Symbol *s)
{
  // TODO zip(iota)
  List<EnumConstDec> *ptr = vals;
  unsigned count = 0;
  while (ptr)
    {
      if (ptr->value->init)
        {
          count = ptr->value->init->evalConst ();
        }
      if (ptr->value->sym == s)
        {
          return new Integer (count);
        }
      else
        {
          count++;
          ptr = ptr->next;
        }
    }
  assert (!"enum constant not found");
  return 0;
}

void
EnumType::makeDef (const char *name, ostream &os)
{
  os << "\nenum " << name << " ";
  displayConsts (os);
  os << ";";
}

// class MvType : public Type (multiple-value type)
// -------------------------------------------

// Data members:  unsigned numVals; Type *type[8];
// 2 <= numVals <= 8; determines number of valid entries of type[].

void
MvType::display (ostream &os) const
{

  assert (type.size () >= 2
          && "It does not make sense to have a mv with 1 or 0 elem");

  os << "<";
  bool first = true;
  for (const auto t : type)
    {
      if (!first)
        {
          os << ", ";
        }
      t->display (os);
    }
  os << ">";
}
