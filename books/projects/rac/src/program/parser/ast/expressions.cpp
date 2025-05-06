#include "expressions.h"
#include "functions.h"
#include "statements.h"
#include "types.h"

#include <algorithm>
#include <sstream>

//***********************************************************************************
// class Expression
//***********************************************************************************

bool Expression::isStaticallyEvaluable() { return false; } // virtual

// Value of expression, applicable to a limited variety of integer-valued
// constant expressions:

int Expression::evalConst() { // virtual (overridden by constant expressions)
  std::cerr << this->loc() << "attempt to evaluate a non-constant expression"
            << std::endl;
  UNREACHABLE();
  return 0;
}

bool Expression::isInteger() { // virtual
  return false;
}

// Translate to an ACL2 assignment with this lvalue and the rvalue given as the
// argument:

Sexpression *
Expression::ACL2Assign([[maybe_unused]] Sexpression
                           *rval) { // virtual (overridden by valid lvalues)
  assert(!"Assigment can be made only to an expression of type SymRef, "
          "ArrayRef, StructRef, or Subrange");
  return nullptr;
}

// If a numerical expression is known to have a non-negative value of bounded
// width, then return the bound; otherwise, return 0:

unsigned Expression::ACL2ValWidth() {
  const Type *t = get_type();
  return t ? t->ACL2ValWidth() : 0;
}

// class Constant : public Expression, public Symbol
// -------------------------------------------------

Constant::Constant(NodesId id, Location loc, const char *n)
    : Expression(id, loc), name_(n) {}
Constant::Constant(NodesId id, Location loc, std::string &&n)
    : Expression(id, loc), name_(std::move(n)) {}

bool Constant::isStaticallyEvaluable() { return true; }

Sexpression *Constant::ACL2Expr() { return new Symbol(name_); }

// class Integer : public Constant
// -------------------------------

Integer::Integer(Location loc, const char *n)
    : Constant(idOf(this), loc, n), val_(0UL) {

  bool sign = false;
  if (n[0] == '-') {
    sign = true;
    ++n;
  }

  unsigned long abs_val;
  char *suffix;
  if (!strncmp(n, "0x", 2)) {
    abs_val = strtol(n, &suffix, 16);
  } else if (!strncmp(n, "0b", 2)) {
    // We skip the prefix.
    abs_val = strtol(n + 2, &suffix, 2);
  } else {
    abs_val = strtol(n, &suffix, 10);
  }

  // If there is a suffix, we copy it and we set name_ to n without the suffix.
  if (*suffix) {
    suffix_ = suffix;
    suffix[0] = '\0';
    name_ = n;
  }

  val_ = BigInt(abs_val, sign);
}

Integer::Integer(Location loc, BigInt n, const std::string &suffix)
    : Constant(idOf(this), loc, to_string(n)), val_(n), suffix_(suffix) {}

int Integer::evalConst() { return val_.eval(); }

void Integer::display(std::ostream &os) const { os << getname(); }

Sexpression *Integer::ACL2Expr() {

  if (!strncmp(getname(), "0x", 2)) {
    std::string new_name(getname());
    new_name[0] = '#';
    Symbol *result = new Symbol(std::move(new_name));
    return result;

  } else if (!strncmp(getname(), "-0x", 3)) {
    std::string new_name(getname() + 1);
    new_name[0] = '#';
    Symbol *result = new Symbol(std::move(new_name));
    return new Plist({&s_minus, result});

  } else {
    return new Symbol(to_string(val_));
  }
}

// class Boolean : public Constant
// -------------------------------
Boolean::Boolean(Location loc, bool value)
    : Constant(idOf(this), loc, std::to_string(value)), value_(value) {}

int Boolean::evalConst() { return value_; }

void Boolean::display(std::ostream &os) const {
  os << (value_ ? "true" : "false");
}

Sexpression *Boolean::ACL2Expr() {
  return new Plist({value_ ? &s_true : &s_false});
}

// class SymRef : public Expression
// ---------------------------------------------------------------

// Reference to declared symbol, which may be an enumeration constant or a
// variable

// Data member: SymDec *symDec;

SymRef::SymRef(Location loc, SymDec *s) : Expression(idOf(this), loc) {
  symDec = s;
}

bool SymRef::isStaticallyEvaluable() { return symDec->isStaticallyEvaluable(); }

int SymRef::evalConst() {
  if (this->isStaticallyEvaluable()) {
    return symDec->evalConst();
  } else {
    std::cerr << this->loc() << "attempt to evaluate a non-constant expression"
              << std::endl;
    UNREACHABLE();
  }
}

bool SymRef::isInteger() { return isIntegerType(get_type()); }

void SymRef::display(std::ostream &os) const { symDec->sym->display(os); }

Sexpression *SymRef::ACL2Expr() {
  Sexpression *s = symDec->ACL2SymExpr();
  return s;
}

Sexpression *SymRef::ACL2Assign(Sexpression *rval) {
  return new Plist({&s_assign, symDec->sym, rval});
}

// class FunCall : public Expression (function call)
// -------------------------------------------------

FunCall::FunCall(Location loc, FunDef *f, std::vector<Expression *> &&a)
    : Expression(idOf(this), loc), func(f), args(a) {}

FunCall::FunCall(NodesId id, Location loc, FunDef *f,
                 std::vector<Expression *> &&a)
    : Expression(id, loc), func(f), args(a) {}

bool FunCall::isInteger() { return isIntegerType(get_type()); }

void FunCall::display(std::ostream &os) const {

  os << func->getname() << '(';
  bool is_first = true;
  std::for_each(args.begin(), args.end(), [&](Expression *e) {
    if (!is_first)
      os << ", ";
    e->display(os);
    is_first = false;
  });

  os << ')';
}

Sexpression *FunCall::ACL2Expr() {

  Plist *result = new Plist({new Symbol(func->getname())});

  auto it = func->params().begin();
  for (Expression *a : args) {
    result->add((*it)->get_type()->cast(a));
    ++it;
  }

  return result;
}

// class TempCall : public Expression (function template Data)
// -------------------------------------------------

TempCall::TempCall(Location loc, Template *f, std::vector<Expression *> &&a,
                   std::vector<Expression *> &&p)
    : FunCall(idOf(this), loc, f, std::move(a)), params(p) {}

void TempCall::display(std::ostream &os) const {
  os << func->getname() << '<';

  bool is_first = true;
  for (Expression *p : params) {
    if (!is_first) {
      os << ", ";
    } else {
      is_first = false;
    }
    p->display(os);
  }
  os << ">(";

  is_first = true;
  for (Expression *a : args) {
    if (!is_first) {
      os << ", ";
    } else {
      is_first = false;
    }
    a->display(os);
  }
  os << ')';
}

Sexpression *TempCall::ACL2Expr() {

  auto template_func = always_cast<Template *>(func);
  template_func->bindParams(params);

  Plist *result = new Plist({new Symbol(func->getname())});

  auto paramsDec = template_func->tempParams();
  for (unsigned i = 0; i < paramsDec.size(); ++i) {
    result->add(paramsDec[i]->get_type()->cast(params[i]));
  }

  auto it = func->params().begin();
  for (Expression *a : args) {
    result->add((*it)->get_type()->cast(a));
    ++it;
  }

  dynamic_cast<Template *>(func)->resetParams();

  return result;
}

// class Initializer : public Expression (array initializer)
// ---------------------------------------------------------

Initializer::Initializer(Location loc, std::vector<Expression *> v)
    : Expression(idOf(this), loc), vals(v) {}

void Initializer::display(std::ostream &os) const {
  os << '{';
  bool first = true;
  for (auto v : vals) {
    if (!first) {
      os << ", ";
    }
    v->ACL2Expr()->display(os);
    first = false;
  }
  os << '}';
}

// In ACL2 arrays, structs accessor returns 0 is no elements are found. We can
// use this behavior for cheap initializer of int/...
bool default_value_can_be_ignored(const Type *t) {
  return isa<const PrimType *>(t) || isa<const IntType *>(t);
}

Sexpression *Initializer::ACL2ArrayExpr(const ArrayType *t,
                                        bool output_optmized_const) {

  Plist *res = new Plist();

  if (output_optmized_const) {

    res->add(&s_list);
    for (auto c : vals) {
      res->add(t->baseType->cast(c));
    }

    return res;

  } else {
    // TODO do not support template
    assert(t->dim->isStaticallyEvaluable());

    res->add(&s_list);

    unsigned size = t->dim->evalConst();
    for (unsigned i = 0; i < size; ++i) {

      if (i < vals.size()) {
        res->add(
            new Cons(Integer(loc_, i).ACL2Expr(), t->baseType->cast(vals[i])));
      } else {

        if (default_value_can_be_ignored(t)) {
          break;
        }

        res->add(new Cons(Integer(t->get_original_location(), i).ACL2Expr(),
                          t->baseType->default_initializer_value()));
      }
    }

    return new Plist({&s_ainit, res});
  }
}

Sexpression *Initializer::ACL2TupleExpr(const MvType *t) {

  Plist *res = new Plist({&s_mv});
  for (unsigned i = 0; i < t->size(); ++i) {
    res->add(t->get(i)->cast(vals[i]));
  }
  return res;
}

Sexpression *Initializer::ACL2StructExpr(const StructType *t) {

  Sexpression *result = new Plist();

  auto v = vals.begin();

  for (auto f : t->fields()) {

    if (v != vals.end()) {
      result = new Plist({&s_as, new Plist({&s_quote, f->get_sym()}),
                          f->get_type()->cast(*v), result});
      ++v;
    } else if (f->get_default_value()) {
      result =
          new Plist({&s_as, new Plist({&s_quote, f->get_sym()}),
                     f->get_type()->cast(*f->get_default_value()), result});
    } else {

      if (default_value_can_be_ignored(f->get_type())) {
        continue;
      }

      result = new Plist({&s_as, new Plist({&s_quote, f->get_sym()}),
                          f->get_type()->default_initializer_value(), result});
    }
  }

  return result;
}

// class ArrayRef : public Expression
// ----------------------------------

// Data members:  Expression *array; Expression *index;

ArrayRef::ArrayRef(Location loc, Expression *a, Expression *i)
    : Expression(idOf(this), loc) {
  array = a;
  index = i;
}

bool ArrayRef::isInteger() { return isIntegerType(get_type()); }

void ArrayRef::display(std::ostream &os) const {
  array->display(os);
  os << '[';
  index->display(os);
  os << ']';
}

Sexpression *ArrayRef::ACL2Expr() {
  if (isa<const ArrayType *>(array->get_type())) {
    Sexpression *s = nullptr;

    SymRef *ref = dynamic_cast<SymRef *>(array);
    if (ref && ref->symDec->get_type()->isConst() && ref->symDec->isGlobal()) {
      s = new Plist({&s_nth, index->ACL2Expr(), new Plist({ref->symDec->sym})});
    } else {
      s = new Plist({&s_ag, index->ACL2Expr(), array->ACL2Expr()});
    }
    return s;
  } else {

    Sexpression *b = array->ACL2Expr();
    Sexpression *i = index->ACL2Expr();

    return new Plist({&s_bitn, b, i});
  }
}

Sexpression *ArrayRef::ACL2Assign(Sexpression *rval) {
  if (isa<const ArrayType *>(array->get_type())) {
    return array->ACL2Assign(
        new Plist({&s_as, index->ACL2Expr(), rval, array->ACL2Expr()}));
  } else {
    Sexpression *b = array->ACL2Expr();
    Sexpression *i = index->ACL2Expr();

    // TODO 2
    const IntType *t = always_cast<const IntType *>(array->get_type());
    unsigned n = t->width()->evalConst();

    Sexpression *s = Integer(loc_, n).ACL2Expr();
    Sexpression *val = new Plist({&s_setbitn, b, s, i, rval});

    return array->ACL2Assign(val);
  }
}

// class StructRef : public Expression
// -----------------------------------

// Data members:  Expression *base; char *field;

StructRef::StructRef(Location loc, Expression *s, char *f)
    : Expression(idOf(this), loc) {
  base = s;
  field = f;
}

bool StructRef::isInteger() { return isIntegerType(get_type()); }

void StructRef::display(std::ostream &os) const {
  base->display(os);
  os << '.' << field;
}

Sexpression *StructRef::ACL2Expr() {
  Symbol *sym = always_cast<const StructType *>(base->get_type())
                    ->getField(field)
                    ->get_sym();

  Sexpression *s =
      new Plist({&s_ag, new Plist({&s_quote, sym}), base->ACL2Expr()});

  return s;
}

Sexpression *StructRef::ACL2Assign(Sexpression *rval) {
  Symbol *sym = always_cast<const StructType *>(base->get_type())
                    ->getField(field)
                    ->get_sym();

  return base->ACL2Assign(
      new Plist({&s_as, new Plist({&s_quote, sym}), rval, base->ACL2Expr()}));
}

// class Subrange : public Expression
// ----------------------------------

// Data members: Expression *base; Expression *high; Expression *low;

Subrange::Subrange(Location loc, Expression *b, Expression *l, Expression *w)
    : Expression(idOf(this), loc), base(b), low(l), width_(w) {
  if (l->isStaticallyEvaluable() && w->isStaticallyEvaluable())
    // TODO 2
    high = new Integer(loc_, l->evalConst() + w->evalConst() - 1);
  else {
    high = new BinaryExpr(
        loc_, l,
        new BinaryExpr(loc_, w, Integer::one_v(loc_), BinaryExpr::Op::Minus),
        BinaryExpr::Op::Plus);
  }
}

void Subrange::display(std::ostream &os) const {
  base->display(os);
  os << '[';
  high->display(os);
  os << ':';
  low->display(os);
  os << ']';
}

Sexpression *Subrange::ACL2Expr() {
  Sexpression *b = base->ACL2Expr();
  Sexpression *hi = high->ACL2Expr();
  Sexpression *lo = low->ACL2Expr();

  return new Plist({&s_bits, b, hi, lo});
}

Sexpression *Subrange::ACL2Assign(Sexpression *rval) {

  Sexpression *b = base->ACL2Expr();
  Sexpression *hi = high->ACL2Expr();
  Sexpression *lo = low->ACL2Expr();

  const IntType *t = always_cast<const IntType *>(base->get_type());

  Sexpression *s = t->width()->ACL2Expr();
  Sexpression *val = new Plist({&s_setbits, b, s, hi, lo, rval});

  return base->ACL2Assign(val);
}

// class PrefixExpr : public Expression
// ------------------------------------

// Data members: Expression *expr; const char *op;

PrefixExpr::PrefixExpr(Location loc, Expression *e, PrefixExpr::Op o)
    : Expression(idOf(this), loc), expr(e), op(o) {}

PrefixExpr::Op PrefixExpr::parseOp(const char *o) {
  if (false) {
  }
#define APPLY_BINARY_OP(_, __)
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(NAME, OP) else if (!strcmp(o, #OP)) return Op::NAME;
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  else
    UNREACHABLE();
}

bool PrefixExpr::isStaticallyEvaluable() {
  return expr->isStaticallyEvaluable();
}

int PrefixExpr::evalConst() {
  int val = expr->evalConst();
  switch (op) {
  case Op::UnaryPlus:
    return val;
  case Op::UnaryMinus:
    return -val;
  case Op::BitNot:
    return -1 - val;
  case Op::Not:
    return val ? 0 : 1;
  default:
    UNREACHABLE();
  }
}

bool PrefixExpr::isInteger() { return expr->isInteger(); }

std::ostream &operator<<(std::ostream &os, PrefixExpr::Op op) {
  switch (op) {
#define APPLY_BINARY_OP(NAME, OP)
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(NAME, OP)                                               \
  case PrefixExpr::Op::NAME:                                                   \
    return os << #OP;
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  default:
    UNREACHABLE();
  }
}

std::string to_string(PrefixExpr::Op op) {
  std::stringstream ss;
  ss << op;
  return ss.str();
}

void PrefixExpr::display(std::ostream &os) const {
  os << op;
  expr->display(os);
}

Sexpression *PrefixExpr::ACL2Expr() {
  Sexpression *s = expr->ACL2Expr();

  if (op == Op::UnaryPlus) {
    return s;
  } else if (op == Op::UnaryMinus) {
    Sexpression *s_val = expr->get_type()->eval(s);
    Sexpression *sexpr = new Plist({&s_minus, s_val});

    if (auto pt = dynamic_cast<const IntType *>(get_type())) {
      Sexpression *upper_bound = nullptr;
      upper_bound =
          pt->width()->isStaticallyEvaluable()
              ? Integer(this->loc(), this->ACL2ValWidth() - 1).ACL2Expr()
              : new Plist({&s_minus, pt->width()->ACL2Expr(), new Symbol(1)});

      sexpr = new Plist({&s_bits, sexpr, upper_bound,
                         Integer::zero_v(this->loc())->ACL2Expr()});
    }

    return sexpr;

  } else if (op == Op::Not) {
    return new Plist({&s_lognot1, s});

  } else if (op == Op::BitNot) {

    Plist *val = new Plist({&s_lognot, expr->ACL2Expr()});

    if (auto pt = dynamic_cast<const IntType *>(get_type())) {
      Sexpression *upper_bound = nullptr;
      upper_bound =
          pt->width()->isStaticallyEvaluable()
              ? Integer(this->loc(), this->ACL2ValWidth() - 1).ACL2Expr()
              : new Plist({&s_minus, pt->width()->ACL2Expr(), new Symbol(1)});

      val = new Plist({&s_bits, val, upper_bound,
                       Integer::zero_v(this->loc())->ACL2Expr()});
    }

    return val;
  } else
    UNREACHABLE();
}

// class CastExpr : public Expression
// ----------------------------------

// Data members: Expression *expr; Type *type;

Sexpression *CastExpr::ACL2Expr() { return type->cast(expr); }

// class BinaryExpr : public Expression
// ------------------------------------

// Data members: Expression *expr1; Expression *expr2; const char *op;

BinaryExpr::BinaryExpr(Location loc, Expression *e1, Expression *e2, Op o)
    : Expression(idOf(this), loc), expr1(e1), expr2(e2), op(o) {}

BinaryExpr::Op BinaryExpr::parseOp(const char *o) {

  if (false) {
  }
#define APPLY_BINARY_OP(NAME, OP) else if (!strcmp(o, #OP)) return Op::NAME;
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(_, __)
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  else
    UNREACHABLE();
}

bool BinaryExpr::isStaticallyEvaluable() {
  return expr1->isStaticallyEvaluable() && expr2->isStaticallyEvaluable();
}

int BinaryExpr::evalConst() {
  int val1 = expr1->evalConst();
  int val2 = expr2->evalConst();

  switch (op) {
#define APPLY_BINARY_OP(NAME, OP)                                              \
  case Op::NAME:                                                               \
    return val1 OP val2;
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(_, __)
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  default:
    UNREACHABLE();
  }
}

std::ostream &operator<<(std::ostream &os, BinaryExpr::Op op) {
  switch (op) {
#define APPLY_BINARY_OP(NAME, OP)                                              \
  case BinaryExpr::Op::NAME:                                                   \
    return os << #OP;
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(_, __)
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  default:
    UNREACHABLE();
  }
}

std::string to_string(BinaryExpr::Op op) {
  std::stringstream ss;
  ss << op;
  return ss.str();
}

bool BinaryExpr::isOpShift(Op o) {
  return o == BinaryExpr::Op::RShift || o == BinaryExpr::Op::LShift;
}

bool BinaryExpr::isOpArithmetic(Op o) {
  return o >= BinaryExpr::Op::Plus && o <= BinaryExpr::Op::Mod;
}

bool BinaryExpr::isOpBitwise(Op o) {
  return o >= BinaryExpr::Op::BitAnd && o <= BinaryExpr::Op::BitOr;
}

bool BinaryExpr::isOpCompare(Op o) {
  return o >= BinaryExpr::Op::Less && o <= BinaryExpr::Op::NotEqual;
}

bool BinaryExpr::isOpLogical(Op o) {
  return o == BinaryExpr::Op::And || o == BinaryExpr::Op::Or;
}

bool BinaryExpr::isInteger() {
  return expr1->isInteger() && expr2->isInteger();
}

void BinaryExpr::display(std::ostream &os) const {
  expr1->display(os);
  os << ' ' << op << ' ';
  expr2->display(os);
}

Sexpression *BinaryExpr::ACL2Expr() {

  Symbol *ptr = nullptr;

  Sexpression *sexpr1 = expr1->ACL2Expr();
  Sexpression *sexpr2 = expr2->ACL2Expr();

  Sexpression *sexpr1_val = expr1->get_type()->eval(expr1->ACL2Expr());
  Sexpression *sexpr2_val = expr2->get_type()->eval(expr2->ACL2Expr());

  bool need_narrowing = true;

  switch (op) {
  case Op::Plus:
    ptr = &s_plus;
    // AC types are guranted to fit in their result type.
    need_narrowing = !isa<const IntType *>(get_type());
    break;
  case Op::Minus:
    ptr = &s_minus;
    // AC types are guranted to fit in their result type.
    need_narrowing = !isa<const IntType *>(get_type());
    break;
  case Op::Times:
    ptr = &s_times;
    // AC types are guranted to fit in their result type.
    need_narrowing = !isa<const IntType *>(get_type());
    break;
  case Op::Divide: {
    Sexpression *val =
        new Plist({&s_truncate, new Plist({&s_slash, sexpr1_val, sexpr2_val}),
                   Integer::one_v(loc_)->ACL2Expr()});
    if (auto pt = dynamic_cast<const PrimType *>(get_type())) {
      (void)pt;
      // For now, we ingore primitive type overflows.
    } else if (auto pt = dynamic_cast<const IntType *>(get_type())) {
      Sexpression *upper_bound = nullptr;
      upper_bound =
          pt->width()->isStaticallyEvaluable()
              ? Integer(this->loc(), this->ACL2ValWidth() - 1).ACL2Expr()
              : new Plist({&s_minus, pt->width()->ACL2Expr(), new Symbol(1)});

      val = new Plist({&s_bits, val, upper_bound,
                       Integer::zero_v(this->loc())->ACL2Expr()});
    }
    return val;
  }
  case Op::Mod:
    // AC types are guranted to fit in their result type.
    need_narrowing = !isa<const IntType *>(get_type());
    ptr = &s_rem;
    break;
  case Op::LShift:
    ptr = &s_ash;
    break;
  case Op::RShift:
    ptr = &s_ash;
    sexpr2_val = new Plist({&s_minus, sexpr2_val});
    break;
  case Op::BitAnd:
    ptr = &s_logand;
    // The result is the same size as the biggest input.
    need_narrowing = false;
    break;
  case Op::BitXor:
    ptr = &s_logxor;
    // The result is the same size as the biggest input.
    need_narrowing = false;
    break;
  case Op::BitOr:
    ptr = &s_logior;
    // The result is the same size as the biggest input.
    need_narrowing = false;
    break;
  case Op::Less:
    ptr = &s_logless;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::Greater:
    ptr = &s_loggreater;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::LessEqual:
    ptr = &s_logleq;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::GreaterEqual:
    ptr = &s_loggeq;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::Equal:
    ptr = &s_logeq;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::NotEqual:
    ptr = &s_logneq;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::And:
    ptr = &s_logand1;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  case Op::Or:
    ptr = &s_logior1;
    // The result is always 0 or 1.
    need_narrowing = false;
    break;
  }

  // TODO why is it needed ? Maybe should be transform to an assert ? But this
  // could make RAC_BYPASS_ERRORS fails. At least, the message should be
  // better.
  //  if (!get_type()) {
  //    (this + 3)->ACL2Expr();
  //    std::cerr << loc();
  //    assert(!"missing type");
  //  }
  Sexpression *val = nullptr;
  if (isOpBitwise(op)) {
    val = new Plist({ptr, sexpr1, sexpr2});
  } else {
    val = new Plist({ptr, sexpr1_val, sexpr2_val});
  }

  const Type *t = get_type();

  if (auto it = dynamic_cast<const IntType *>(t)) {
    if (it->isSigned()->isStaticallyEvaluable()) {
      if (it->isSigned()->evalConst()) {
        need_narrowing = true;
      }
    } else {
      need_narrowing = true;
    }
  }

  if (need_narrowing) {
    if (auto pt = dynamic_cast<const PrimType *>(t)) {
      (void)pt;
      // For now, we ingore primitive type overflows.
    } else if (auto pt = dynamic_cast<const IntType *>(t)) {
      Sexpression *upper_bound = nullptr;
      upper_bound =
          pt->width()->isStaticallyEvaluable()
              ? Integer(this->loc(), this->ACL2ValWidth() - 1).ACL2Expr()
              : new Plist({&s_minus, pt->width()->ACL2Expr(), new Symbol(1)});

      val = new Plist({&s_bits, val, upper_bound,
                       Integer::zero_v(this->loc())->ACL2Expr()});
    }
  }

  return val;
}

// class CondExpr : public Expression (conditional expression)
// -----------------------------------------------------------

// Data members:  Expression *expr1; Expression *expr2; Expression *test;

CondExpr::CondExpr(Location loc, Expression *e1, Expression *e2, Expression *t)
    : Expression(idOf(this), loc) {
  expr1 = e1;
  expr2 = e2;
  test = t;
}

bool CondExpr::isInteger() { return expr1->isInteger() && expr2->isInteger(); }

void CondExpr::display(std::ostream &os) const {
  test->display(os);
  os << " ? ";
  expr1->display(os);
  os << " : ";
  expr2->display(os);
}

Sexpression *CondExpr::ACL2Expr() {
  return new Plist(
      {&s_if1, test->ACL2Expr(), expr1->ACL2Expr(), expr2->ACL2Expr()});
}

int CondExpr::evalConst() {
  return test->evalConst() ? expr1->evalConst() : expr2->evalConst();
}

// class MultipleValue : public Expression
// ---------------------------------------

MultipleValue::MultipleValue(Location loc, const MvType *t,
                             std::vector<Expression *> &&e)
    : Expression(idOf(this), loc), expr_(e) {
  set_type(t);
}

void MultipleValue::display(std::ostream &os) const {

  os << '<';
  bool first = true;
  for (const auto e : expr_) {
    if (!first) {
      os << ", ";
    }
    e->display(os);
    first = false;
  }
  os << '>';
}

Sexpression *MultipleValue::ACL2Expr() {

  Plist *result = new Plist({&s_mv});

  const MvType *t = static_cast<const MvType *>(get_type());
  auto types_and_expr = Zip(t->types(), expr_);
  std::for_each(types_and_expr.begin(), types_and_expr.end(),
                [&](const auto &p) {
                  auto [type, expr] = p;
                  result->add(type->cast(expr));
                });

  return result;
}
