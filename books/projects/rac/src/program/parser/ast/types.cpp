#include "types.h"

#include "expressions.h"
#include "statements.h"

#include <algorithm>
#include <iomanip>
#include <sstream>

//***********************************************************************************
// class Type
//***********************************************************************************

static bool disable_optimizations = std::getenv("RAC_DISABLE_OPTIMIZATIONS");

std::string Type::to_string() const {
  std::stringstream ss;

  // TODO
  //  auto cur = origin_;
  //  while (std::holds_alternative<const DefinedType *>(cur)) {
  //    auto dt = std::get<const DefinedType *>(cur);
  //    ss << dt->getname() << " aka ";
  //    cur = dt->origin_;
  //  }

  display(ss);
  return ss.str();
}

Sexpression *
Type::cast(Expression *rval) const { // virtual (overridden by IntType)
  // Convert rval to an S-expression to be assigned to an object of this type.
  return rval->ACL2Expr();
}

void Type::displayVarType(std::ostream &os) const {
  // How this type is displayed in a variable declaration

  if (isConst()) {
    os << "const ";
  }

  display(os);
}

void Type::displayVarName(const char *name, std::ostream &os) const {

  if (isConst()) {
    os << "const ";
  }
  os << name;
}

// overridden by ArrayType, StructType, and EnumType
void Type::makeDef([[maybe_unused]] const char *name, std::ostream &os) const {
  // How this type is displayed in a type definition.
  os << "\ntypedef ";
  display(os);
  os << " " << name << ";";
}

Location Type::get_original_location() const {

  auto cur = origin_;
  while (std::holds_alternative<const DefinedType *>(cur)) {
    auto dt = std::get<const DefinedType *>(cur);
    cur = dt->origin_;
  }

  return std::get<Location>(cur);
}

// class PrimType : public Symbol, public Type (Primitive type)
// ------------------------------------------------------------

PrimType *boolType = PrimType::Bool();
PrimType *intType = PrimType::Int();
PrimType *uintType = PrimType::Uint();
PrimType *int64Type = PrimType::Int64();
PrimType *uint64Type = PrimType::Uint64();

Sexpression *PrimType::cast(Expression *rval) const {

  const Type *rval_type = rval->get_type();
  Sexpression *sexpr = rval->ACL2Expr();

  int w_dst = static_cast<std::underlying_type_t<PrimType::Rank>>(rank_);

  // If they are the same no conversion needed.
  if (rval_type->isEqual(this)) {
    return sexpr;
  }

  // If rval is a constant we are able to make optimize based on its value
  // rather its type.
  if (auto c = dynamic_cast<Constant *>(rval)) {
    if (c->fitInside(signed_, w_dst)) {
      return sexpr;
    }
  }

  // If the destination is a bool, we should ensure that the result if
  // always_cast zero or one. TODO
  if (rank_ == PrimType::Rank::Bool) {
    return sexpr;
    //  return new Plist(
    //  { &s_if1, sexpr, new Plist({ &s_true }), new Plist({ &s_false })
    //  });
  }

  Location loc = get_original_location();

  // Get type's informations (we may not the value if the type is templated):
  Expression *w_src = nullptr;
  Expression *s_src = nullptr;

  if (auto pt = dynamic_cast<const PrimType *>(rval_type)) {
    int val = static_cast<std::underlying_type_t<PrimType::Rank>>(pt->rank_);
    w_src = new Integer(loc, val);
    s_src = new Boolean(loc, pt->signed_);
  } else {
    auto rt = always_cast<const IntType *>(rval_type);
    w_src = rt->width();
    s_src = rt->isSigned();
  }

  bool are_static =
      w_src->isStaticallyEvaluable() && s_src->isStaticallyEvaluable();

  std::optional<int> w_src_val = w_src->isStaticallyEvaluable()
                                     ? std::optional{w_src->evalConst()}
                                     : std::nullopt;
  std::optional<bool> s_src_val =
      s_src->isStaticallyEvaluable()
          ? std::optional(static_cast<bool>(s_src->evalConst()))
          : std::nullopt;

  // First, we need to get the value begin the type: if it is a PrimType or an
  // unsigned register, we have nothing to do since they already have their
  // value. We only need to add a `si` for the signed registers.
  Sexpression *value = nullptr;

  // Known at compile time.
  if (s_src_val) {
    if (isa<const IntType *>(rval_type) && *s_src_val) {
      value = new Plist({&s_si, sexpr, w_src->ACL2Expr()});
    } else {
      value = sexpr;
    }
  } else {
    value = new Plist({&s_if, s_src->ACL2Expr(),
                       new Plist({&s_si, sexpr, w_src->ACL2Expr()}), sexpr});
  }

  // Check if we need to do some conversion to fit the source into the
  // destination (sign and width).
  bool src_fit_inside_dst = false;

  if (!disable_optimizations) {
    if (are_static) {
      // Always true (implied by `are_static`) but makes gcc and clang happy by
      // removing a -Wmaybe-uninitialized error.
      assert(s_src_val);
      assert(w_src_val);
      if (*s_src_val == signed_ && w_dst >= *w_src_val) {
        src_fit_inside_dst = true;
      }

      if (signed_ && !(*s_src_val) && w_dst > *w_src_val) {
        src_fit_inside_dst = true;
      }
    }
    // else:
    // If the source value is signed and the destination unsigned we always
    // need a cast.
  }

  Sexpression *res = value;
  if (!src_fit_inside_dst) {
    Sexpression *upper_bound = Integer(loc, w_dst - 1).ACL2Expr();
    res = new Plist(
        {&s_bits, res, upper_bound, Integer::zero_v(loc)->ACL2Expr()});

    if (signed_) {
      res = new Plist(
          {&s_si, res, Integer(get_original_location(), w_dst).ACL2Expr()});
    }
  }

  return res;
}

bool PrimType::isEqual(const Type *other) const {

  if (auto o = dynamic_cast<const DefinedType *>(other)) {
    other = o->derefType();
  }

  if (auto o = dynamic_cast<const PrimType *>(other)) {
    return rank_ == o->rank_ && signed_ == o->signed_;
  } else {
    return false;
  }
}

Type *PrimType::usual_conversions(const PrimType *t1, const PrimType *t2,
                                  bool integer_promotion) {

  // Integer promotion.
  PrimType *t1_promoted = t1->deep_copy();
  if (integer_promotion) {
    t1_promoted->integerPromtion();
  }

  PrimType *t2_promoted = t2->deep_copy();
  if (integer_promotion) {
    t2_promoted->integerPromtion();
  }

  // If T1 and T2 are the same type, C is that type.
  // Otherwise, if T1 and T2 are both signed integer types or both unsigned
  // integer types, C is the type of greater integer conversion rank.
  if (t1_promoted->signed_ == t2_promoted->signed_) {
    if (t1_promoted->rank_ >= t2_promoted->rank_) {
      delete t2_promoted;
      return t1_promoted;
    } else {
      delete t1_promoted;
      return t2_promoted;
    }
  }

  PrimType *unsigned_type = nullptr;
  PrimType *signed_type = nullptr;
  if (t1_promoted->signed_) {
    unsigned_type = t2_promoted;
    signed_type = t1_promoted;
  } else {
    unsigned_type = t1_promoted;
    signed_type = t2_promoted;
  }

  // If the integer conversion rank of U is greater than or equal to the
  // integer conversion rank of S, C is U.
  if (unsigned_type->rank_ >= signed_type->rank_) {
    delete signed_type;
    return unsigned_type;
  } else {
    // Otherwise, if S can represent all of the values of U, C is S.
    delete unsigned_type;
    return signed_type;
  }
}

bool PrimType::canBeImplicitlyCastTo(const Type *target) const {

  // We can convert to any size, even if it is a narrowing conversion.
  if (isa<const PrimType *>(target)) {
    return true;
  }

  if (isa<const IntType *>(target)) {
    return true;
  }

  return false;
}

Sexpression *PrimType::default_initializer_value() const {
  return Integer::zero_v(Location::builtin())->ACL2Expr();
}

// class IntType : public Type
// -------------------------------

IntType *IntType::FromPrimType(const PrimType *t) {
  auto loc = t->get_original_location();
  return new IntType({t->loc()}, new Integer(loc, static_cast<int>(t->rank_)),
                     new Boolean(loc, t->signed_));
}

void IntType::display(std::ostream &os) const {
  if (isConst()) {
    os << "const ";
  }
  os << "ac_int<";
  width()->display(os);
  os << (isSigned_->evalConst() ? ", true>" : ", false>");
}

unsigned IntType::ACL2ValWidth() const {
  assert(width()->isStaticallyEvaluable() && "static evaluation failed.\n");
  return width()->evalConst();
}

Sexpression *IntType::cast(Expression *rval) const {

  // Try to figure out if the bits/si are really necessary.
  const Type *rval_type = rval->get_type();

  if (rval_type->isEqual(this)) {
    return rval->ACL2Expr();
  }

  if (!disable_optimizations) {
    // The size must be known.
    if (this->width()->isStaticallyEvaluable()) {
      unsigned w_dst = this->ACL2ValWidth();

      // If rval is a constant we are able to make optimize based on its value
      // rather its type. The constant should not be signed.
      if (this->isSigned()->isStaticallyEvaluable()) {
        bool s = this->isSigned()->evalConst();
        if (!s) {
          if (auto c = dynamic_cast<Constant *>(rval)) {
            if (c->fitInside(s, w_dst)) {
              return rval->ACL2Expr();
            }
          }

          // Check if a register fit inside another.
          if (auto p = dynamic_cast<const IntType *>(rval_type)) {
            if (p->width()->isStaticallyEvaluable() &&
                p->isSigned()->isStaticallyEvaluable() &&
                !p->isSigned()->evalConst() &&
                rval_type->ACL2ValWidth() <= w_dst) {
              return rval->ACL2Expr();
            }
          }
        }
      }

      // Checks if a PrimType does not needs to be converted from a signed
      // value to its binnary represenation and if it fits inside this.
      if (auto p = dynamic_cast<const PrimType *>(rval_type)) {
        if (!p->signed_ && p->ACL2ValWidth() <= w_dst) {
          return rval->ACL2Expr();
        }
      }
    }
  }

  Location loc = get_original_location();

  Sexpression *sexpr = rval_type->eval(rval->ACL2Expr());

  Sexpression *upper_bound = nullptr;
  upper_bound =
      this->width()->isStaticallyEvaluable()
          ? Integer(loc, this->ACL2ValWidth() - 1).ACL2Expr()
          : new Plist({&s_minus, this->width()->ACL2Expr(), new Symbol(1)});

  Sexpression *res = new Plist(
      {&s_bits, sexpr, upper_bound, Integer::zero_v(loc)->ACL2Expr()});

  return res;
}

Sexpression *IntType::eval(Sexpression *sexpr) const {

  if (isSigned_->isStaticallyEvaluable()) {
    if (isSigned_->evalConst()) {
      auto w = width_->isStaticallyEvaluable()
                   ? new Integer(get_original_location(), width_->evalConst())
                   : width_;
      return new Plist({&s_si, sexpr, w->ACL2Expr()});
    } else {
      return sexpr;
    }
  }

  return new Plist({&s_if1, isSigned_->ACL2Expr(),
                    new Plist({&s_si, sexpr, width_->ACL2Expr()}), sexpr});
}

bool IntType::isEqual(const Type *other) const {
  if (auto o = dynamic_cast<const DefinedType *>(other)) {
    other = o->derefType();
  }

  if (auto o = dynamic_cast<const IntType *>(other)) {
    if (width_->isStaticallyEvaluable() && o->width_->isStaticallyEvaluable() &&
        isSigned_->isStaticallyEvaluable() &&
        o->isSigned_->isStaticallyEvaluable()) {
      return width_->evalConst() == o->width_->evalConst() &&
             isSigned_->evalConst() == o->isSigned_->evalConst();
    } else {
      return false;
    }
  } else {
    return false;
  }
}

// Type integer register type according to ac_datatypes_ref section 2.3.7.
// The AC library only defines long long and unsigned long long operator but
// since they can be casted to any smaller types, we assume this is possible.
// If the register depends on template parameter, we always need an explicit
// cast.
bool IntType::canBeImplicitlyCastTo(const Type *target) const {
  if (isa<const PrimType *>(target)) {
    if (width_->isStaticallyEvaluable()) {
      return width_->evalConst() <= 64;
    } else {
      return false;
    }
  }
  return isa<const IntType *>(target);
}

Sexpression *IntType::default_initializer_value() const {
  // TODO location
  return Integer::zero_v(get_original_location())->ACL2Expr();
}

// class ArrayType : public Type
// -----------------------------

// Data members: Type *baseType; Expresion *dim;

void ArrayType::display(std::ostream &os) const {

  if (isConst()) {
    os << "const ";
  }
  baseType->display(os);
  os << "[";
  dim->display(os);
  os << "]";
}

void ArrayType::displayVarType(std::ostream &os) const {

  if (isConst()) {
    os << "const ";
  }
  baseType->display(os);
}

void ArrayType::displayVarName(const char *name, std::ostream &os) const {
  os << name << '[';
  dim->display(os);
  os << ']';
}

void ArrayType::makeDef(const char *name, std::ostream &os) const {
  os << "\ntypedef ";
  baseType->display(os);
  os << " " << name;

  std::vector<Expression *> dims;
  for (auto b = this; b; b = dynamic_cast<const ArrayType *>(b->baseType)) {
    dims.push_back(b->dim);
  }

  for (auto it = dims.begin(); it != dims.end(); ++it) {
    os << "[";
    (*it)->display(os);
    os << "]";
  }

  os << ";";
}

bool ArrayType::isEqual(const Type *other) const {
  if (auto o = dynamic_cast<const DefinedType *>(other)) {
    other = o->derefType();
  }

  if (auto o = dynamic_cast<const ArrayType *>(other)) {
    return dim->evalConst() == o->dim->evalConst() &&
           baseType->isEqual(o->baseType);
  } else {
    return false;
  }
}

Sexpression *ArrayType::cast(Expression *rval) const {

  if (auto init = dynamic_cast<Initializer *>(rval)) {
    return init->ACL2ArrayExpr(this, isConst());
  } else {
    return rval->ACL2Expr();
  }
}

Sexpression *ArrayType::default_initializer_value() const {

  Plist *result = new Plist({});

  // TODO do not support template
  assert(dim->isStaticallyEvaluable());

  unsigned size = dim->evalConst();
  for (unsigned i = 0; i < size; ++i) {
    result->add(new Cons(Integer(get_original_location(), i).ACL2Expr(),
                         baseType->default_initializer_value()));
  }

  return new Plist({&s_quote, result});
}

// class StructField
// -----------------

void StructField::display(std::ostream &os, unsigned indent) const {
  if (indent)
    os << std::setw(indent) << " ";

  if (type_->isConst()) {
    os << "const ";
  }
  type_->display(os);
  os << " " << getname() << ";";
}

// class StructType : public Type
// ------------------------------

// Data member:  List<StructField> *fields;

void StructType::displayFields(std::ostream &os) const {
  os << "{";
  bool first = true;
  for (const auto &f : fields_) {
    if (!first)
      os << " ";
    f->display(os);
    first = false;
  }
  os << "}";
}

void StructType::display(std::ostream &os) const {
  if (isConst()) {
    os << "const ";
  }
  os << "struct ";
  this->displayFields(os);
}

void StructType::makeDef(const char *name, std::ostream &os) const {
  if (isConst()) {
    os << "const ";
  }

  os << "\nstruct " << name << " ";
  displayFields(os);
  os << ";";
}

const StructField *StructType::getField(const std::string &name) const {
  auto it = std::find_if(fields_.begin(), fields_.end(),
                         [&](auto f) { return f->getname() == name; });
  assert(it != fields_.end());
  return *it;
}

bool StructType::isEqual(const Type *other) const {
  if (auto o = dynamic_cast<const DefinedType *>(other)) {
    other = o->derefType();
  }

  if (auto o = dynamic_cast<const StructType *>(other)) {
    if (fields_.size() != o->fields_.size()) {
      return false;
    }

    for (unsigned i = 0; i < fields_.size(); ++i) {
      if (fields_[i] != o->fields_[i]) {
        return false;
      }
    }

    return true;
  }

  return false;
}

Sexpression *StructType::cast(Expression *rval) const {

  if (auto init = dynamic_cast<Initializer *>(rval)) {
    return init->ACL2StructExpr(this);
  } else {
    return rval->ACL2Expr();
  }
}

Sexpression *StructType::default_initializer_value() const {

  Plist *result = new Plist({});

  for (const auto &f : fields_) {
    if (f->get_default_value()) {
      auto default_value = *f->get_default_value();
      assert(f->get_type());
      assert(default_value);
      auto val = f->get_type()->cast(default_value);
      result =
          new Plist({&s_as, new Plist({&s_quote, f->get_sym()}), val, result});
    } else {
      result = new Plist({&s_as, new Plist({&s_quote, f->get_sym()}),
                          f->get_type()->default_initializer_value(), result});
    }
  }

  return result;
}

// class EnumType : public Type
// ----------------------------

// Data member:  List<EnumConstDec> *vals;

EnumType::EnumType(origin_t loc, std::vector<EnumConstDec *> v)
    : PrimType(loc, idOf(this), "enum", {}, PrimType::Rank::Int, true),
      vals_(v) {
  std::for_each(vals_.begin(), vals_.end(),
                [this](EnumConstDec *e) { e->set_type(this); });
}

Sexpression *EnumType::ACL2Expr() {
  Plist *result = new Plist();
  std::for_each(vals_.begin(), vals_.end(),
                [result](EnumConstDec *e) { result->add(e->ACL2Expr()); });
  return result;
}

void EnumType::displayConsts(std::ostream &os) const {
  os << "{";
  bool is_first = true;
  std::for_each(vals_.begin(), vals_.end(), [&](EnumConstDec *e) {
    if (!is_first)
      os << ", ";
    e->display(os, 0);
    is_first = false;
  });
  os << "}";
}

void EnumType::display(std::ostream &os) const {
  if (isConst()) {
    os << "const ";
  }

  os << "enum ";
  displayConsts(os);
}

Sexpression *EnumType::getEnumVal(Symbol *s) const {
  int count = 0;
  for (auto d : vals_) {
    if (d->init)
      count = d->init->evalConst();
    if (d->sym == s)
      return Integer(get_original_location(), count).ACL2Expr();
    else
      count++;
  }
  assert(!"enum constant not found");
  return 0;
}

void EnumType::makeDef(const char *name, std::ostream &os) const {
  if (isConst()) {
    os << "const ";
  }

  os << "\nenum " << name << " ";
  displayConsts(os);
  os << ";";
}

bool EnumType::isEqual(const Type *other) const {
  if (auto o = dynamic_cast<const DefinedType *>(other)) {
    other = o->derefType();
  }

  if (auto o = dynamic_cast<const EnumType *>(other)) {
    if (vals_.size() != o->vals_.size()) {
      return false;
    }

    for (unsigned i = 0; i < vals_.size(); ++i) {
      // TODO this is wrong (we are comparing the pointers and not the values)
      // but should be correct in most of the cases. Anyway this can make valid
      // code not compile but not the inverse so, the result is always sane.
      if (vals_[i] != o->vals_[i]) {
        return false;
      }
    }
    return true;
  }

  return false;
}

Sexpression *EnumType::default_initializer_value() const {
  return Integer::zero_v(get_original_location())->ACL2Expr();
}

namespace priv {
// class CompositeType : public Type (multiple-value type)
// -------------------------------------------

void CompositeType::display(std::ostream &os) const {

  os << "<";
  bool first = true;
  for (const auto t : types_) {
    if (!first) {
      os << ", ";
    }

    if (t->isConst()) {
      os << "const ";
    }

    t->display(os);
    first = false;
  }
  os << ">";
}

bool CompositeType::isEqual(const Type *other) const {

  if (auto o = dynamic_cast<const DefinedType *>(other)) {
    other = o->derefType();
  }

  if (auto o = dynamic_cast<const CompositeType *>(other)) {
    if (types_.size() != o->types_.size()) {
      return false;
    }

    for (unsigned i = 0; i < types_.size(); ++i) {
      if (!types_[i]->isEqual(o->types_[i])) {
        return false;
      }
    }
    return true;
  }

  return false;
}
} // namespace priv

Sexpression *MvType::cast(Expression *rval) const {
  if (auto init = dynamic_cast<Initializer *>(rval)) {
    return init->ACL2TupleExpr(this);
  } else {
    return rval->ACL2Expr();
  }
}

Sexpression *MvType::default_initializer_value() const {

  Plist *res = new Plist({&s_mv});
  for (unsigned i = 0; i < size(); ++i) {
    res->add(get(i)->default_initializer_value());
  }
  return res;
}
