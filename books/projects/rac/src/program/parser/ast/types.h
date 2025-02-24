#ifndef TYPES_H
#define TYPES_H

#include "../../sexpressions.h"
#include "../utils/diagnostics.h"

#include "nodesid.h"

#include <algorithm>
#include <iostream>
#include <optional>
#include <variant>

//***********************************************************************************
// Types
//***********************************************************************************

class Expression;
class EnumConstDec;
class DefinedType;

// Derived classes:
//
//   PrimType           (primitive type: uintType, intType, boolType)
//   DefinedType        (introduced by typedef)
//   IntType            (limited integer register)
//   ArrayType          (array type)
//   StructType         (struct type) EnumType (enumeration type)
//   MvType             (multiple value type)
//   InitializerType    (type of initializer list)
//   ErrorType          (type used to recover from typing error)
class Type {

public:
  using origin_t = std::variant<const DefinedType *, Location>;

  Type(origin_t loc, NodesId id) : origin_(loc), id_(id) {}
  virtual ~Type() {}
  virtual Type *deep_copy() const = 0;
  virtual bool isEqual(const Type *other) const = 0;

  NodesId id() const { return id_; }

  const origin_t &loc() const { return origin_; }
  Location get_original_location() const;

  void setConst() { isConst_ = true; }
  bool isConst() const { return isConst_; }

  // Display the type (but not it is not the C++ representation).
  virtual void display(std::ostream &os = std::cout) const = 0;
  std::string to_string() const;

  // Display a (or multiple) variable definition.
  virtual void displayVarType(std::ostream &os = std::cout) const;
  virtual void displayVarName(const char *name,
                              std::ostream &os = std::cout) const;

  // Display a type defintion (either a typedef for primitive types, array
  // enum or struct definition).
  virtual void makeDef([[maybe_unused]] const char *name,
                       std::ostream &os = std::cout) const;

  // overridden by IntType
  // Convert rval to an S-expression to be assigned to an object of this
  virtual bool canBeImplicitlyCastTo(const Type *target) const = 0;
  virtual Sexpression *cast(Expression *rval) const;
  virtual Sexpression *eval(Sexpression *sexpr) const { return sexpr; }
  virtual Sexpression *default_initializer_value() const = 0;

  // TODO refactore.
  // overridden by IntType
  virtual unsigned ACL2ValWidth() const {

    // Boundary on the width of the value of an object of this type.
    // Used to avoid unnecessary call to bits.
    return 0;
  }

  // TODO
  mutable origin_t origin_;

private:
  const NodesId id_;
  bool isConst_ = false;
};

class PrimType : public Symbol, public Type {

public:
  enum class Rank {
    Bool = 1,
    Int = 32,
    Long = 64,
  };

  PrimType(origin_t loc, const char *name, const char *m, Rank r, bool s)
      : Symbol(name), Type(loc, idOf(this)),
        RACname_(m ? std::optional(std::string(m)) : std::nullopt), rank_(r),
        signed_(s) {}

  PrimType(origin_t loc, NodesId id, const char *name, const char *m, Rank r,
           bool s)
      : Symbol(name), Type(loc, id),
        RACname_(m ? std::optional(std::string(m)) : std::nullopt), rank_(r),
        signed_(s) {}

  virtual ~PrimType() {}

  virtual PrimType *deep_copy() const override { return new PrimType(*this); }

  static PrimType *Bool() {
    return new PrimType(Location::builtin(), "bool", nullptr, Rank::Bool, false);
  }
  static PrimType *Int() {
    return new PrimType(Location::builtin(), "int", nullptr, Rank::Int, true);
  }
  static PrimType *Uint() {
    return new PrimType(Location::builtin(), "uint", nullptr, Rank::Int, false);
  }
  static PrimType *Int64() {
    return new PrimType(Location::builtin(), "int64", "int64", Rank::Long, true);
  }
  static PrimType *Uint64() {
    return new PrimType(Location::builtin(), "uint64", "uint64", Rank::Long, false);
  }

  Sexpression *cast(Expression *rval) const override;

  virtual void display(std::ostream &os) const override {

    if (RACname_) {

      if (isConst()) {
        os << "const ";
      }

      os << *RACname_;
    } else {
      Symbol::display(os);
    }
  }

  // Integer promotion: all the type below int are transformed to an int.
  void integerPromtion() {
    if (rank_ < Rank::Int) {
      rank_ = Rank::Int;
      signed_ = true;
      setName("int");
    }
  }

  virtual unsigned ACL2ValWidth() const override {
    return static_cast<unsigned>(rank_);
  }

  virtual bool isEqual(const Type *other) const override;
  virtual bool canBeImplicitlyCastTo(const Type *target) const override;

  // https://en.cppreference.com/w/cpp/language/usual_arithmetic_conversions
  // Return a new type.
  static Type *usual_conversions(const PrimType *t1, const PrimType *t2,
                                 bool integer_promotion = true);

  Sexpression *default_initializer_value() const override;

  const std::optional<std::string> RACname_;
  Rank rank_;
  bool signed_;
};

extern PrimType boolType;
extern PrimType intType;
extern PrimType uintType;
extern PrimType int64Type;
extern PrimType uint64Type;

class DefinedType final : public Symbol, public Type {
public:
  DefinedType(origin_t loc, const char *s, const Type *t)
      : Symbol(s), Type(loc, idOf(this)), def_(t) {}

  ~DefinedType() {}

  Type *deep_copy() const override {
    auto tmp = new DefinedType(*this);
    if (def_) {
      tmp->def_ = def_->deep_copy();
    } else {
      tmp->def_ = nullptr;
    }
    return tmp;
  }

  void display(std::ostream &os) const override { Symbol::display(os); }

  void displayVarType(std::ostream &os = std::cout) const override {

    if (isConst()) {
      os << "const ";
    }

    os << getname();
  }

  void displayVarName(const char *name,
                      std::ostream &os = std::cout) const override {
    os << name;
  }

  void makeDef(const char *name, std::ostream &os = std::cout) const override {
    derefType()->makeDef(name, os);
  }

  virtual Sexpression *cast(Expression *rval) const override {
    return derefType()->cast(rval);
  }

  unsigned ACL2ValWidth() const override { return derefType()->ACL2ValWidth(); }

  void displayDef(std::ostream &os = std::cout) const {
    def_->makeDef(getname(), os);
  }

  const Type *getdef() const { return def_; }

  const Type *derefType() const {

    const Type *t = def_;
    t->origin_ = this;

    while (auto *dt = dynamic_cast<const DefinedType *>(t)) {
      t = dt->getdef();
      t->origin_ = dt;
    }
    return t;
  }

  // TODO
  bool isEqual(const Type *other) const override {
    return derefType()->isEqual(other);
  }
  bool canBeImplicitlyCastTo(const Type *target) const override {
    return derefType()->canBeImplicitlyCastTo(target);
  }

  Sexpression *default_initializer_value() const override {
    return def_->default_initializer_value();
  }

private:
  const Type *def_;
};

class IntType final : public Type {
public:
  IntType(origin_t loc, Expression *w, Expression *s)
      : Type(loc, idOf(this)), width_(w), isSigned_(s) {}

  ~IntType() {}

  Type *deep_copy() const override {
    // TODO
    return new IntType(*this);
  }

  // Return an ac_int of the same sign and width as t.
  static IntType *FromPrimType(const PrimType *t);

  void display(std::ostream &os = std::cout) const override;
  Sexpression *cast(Expression *rval) const override;

  unsigned ACL2ValWidth() const override;

  Expression *isSigned() const { return isSigned_; }
  Expression *width() const { return width_; }

  Sexpression *eval(Sexpression *sexpr) const override;

  bool isEqual(const Type *other) const override;
  bool canBeImplicitlyCastTo(const Type *target) const override;

  Sexpression *default_initializer_value() const override;

private:
  Expression *width_;
  Expression *isSigned_;
};

class ArrayType final : public Type {
public:
  const Type *baseType;
  Expression *dim;

  ArrayType(origin_t loc, Expression *d, const Type *t)
      : Type(loc, idOf(this)), baseType(t), dim(d) {}

  ~ArrayType() {}

  Type *deep_copy() const override {
    auto tmp = new ArrayType(*this);
    if (tmp->baseType) {
      tmp->baseType = baseType->deep_copy();
    } else {
      tmp->baseType = nullptr;
    }

    return tmp;
  }

  const Type *getBaseType() { return baseType; }
  const Type *getBaseType() const { return baseType; }

  void display(std::ostream &os) const override;
  void displayVarType(std::ostream &os = std::cout) const override;
  void displayVarName(const char *name,
                      std::ostream &os = std::cout) const override;
  void makeDef(const char *name, std::ostream &os) const override;

  bool isEqual(const Type *other) const override;

  bool
  canBeImplicitlyCastTo([[maybe_unused]] const Type *target) const override {
    return false;
  }

  virtual Sexpression *cast(Expression *rval) const override;

  inline void setSTDArray() { isSTDarray_ = true; }
  inline bool isSTDArray() const { return isSTDarray_; }

  Sexpression *default_initializer_value() const override;

private:
  bool isSTDarray_ = false;
};

class StructField {
public:
  StructField(const Type *t, const char *n)
      : sym_(new Symbol(n)), type_(t), default_value_() {}
  StructField(const Type *t, const char *n, Expression *default_value)
      : sym_(new Symbol(n)), type_(t), default_value_(default_value) {}
  ~StructField() {}

  const char *getname() const { return sym_->getname(); }
  Symbol *get_sym() const { return sym_; }
  const Type *get_type() const { return type_; }
  std::optional<Expression *> get_default_value() const {
    return default_value_;
  }

  void display(std::ostream &os, unsigned indent = 0) const;

  bool operator==(const StructField &other) const {
    return strcmp(sym_->getname(), other.getname()) &&
           type_->isEqual(other.type_);
  }

private:
  Symbol *sym_;
  const Type *type_;
  std::optional<Expression *> default_value_;
};

class StructType final : public Type {
public:
  StructType(origin_t loc, std::vector<StructField *> f)
      : Type(loc, idOf(this)), fields_(f) {}
  ~StructType() {}

  Type *deep_copy() const override { return new StructType(*this); }

  void displayFields(std::ostream &os) const;
  void display(std::ostream &os) const override;
  void makeDef(const char *name, std::ostream &os = std::cout) const override;

  const std::vector<StructField *> &fields() const { return fields_; }

  const StructField *getField(const std::string &name) const;

  bool isEqual(const Type *) const override;

  bool
  canBeImplicitlyCastTo([[maybe_unused]] const Type *target) const override {
    return false;
  }

  virtual Sexpression *cast(Expression *rval) const override;

  Sexpression *default_initializer_value() const override;

private:
  std::vector<StructField *> fields_;
};

class EnumType final : public PrimType {
public:
  EnumType(origin_t loc, std::vector<EnumConstDec *> v);
  ~EnumType() {}

  PrimType *deep_copy() const override { return new EnumType(*this); }

  void displayConsts(std::ostream &os) const;
  void display(std::ostream &os) const override;
  void makeDef(const char *name, std::ostream &os = std::cout) const override;

  Sexpression *ACL2Expr();

  Sexpression *getEnumVal(Symbol *s) const;

  bool canBeImplicitlyCastTo(const Type *target) const override {
    return isa<const PrimType *>(target);
  }

  bool isEqual(const Type *) const override;

  const std::vector<EnumConstDec *> &values() const { return vals_; }

  Sexpression *default_initializer_value() const override;

private:
  std::vector<EnumConstDec *> vals_;
};

namespace priv {
class CompositeType : public Type {
public:
  CompositeType(origin_t loc, NodesId id, std::vector<const Type *> &&t)
      : Type(loc, id), types_(t) {}
  virtual ~CompositeType() {}

  void display(std::ostream &os) const override;

  unsigned size() const { return types_.size(); }
  const Type *get(unsigned n) const { return types_[n]; }
  const Type *get(unsigned n) { return types_[n]; }
  const std::vector<const Type *> &types() const { return types_; }

  bool isEqual(const Type *other) const override;

  bool
  canBeImplicitlyCastTo([[maybe_unused]] const Type *target) const override {
    return false;
  }

private:
  std::vector<const Type *> types_;
};
} // namespace priv

class MvType final : public priv::CompositeType {
public:
  MvType(origin_t loc, std::vector<const Type *> &&t)
      : CompositeType(loc, idOf(this), std::move(t)) {}
  ~MvType() {}

  Type *deep_copy() const override {

    std::vector<const Type *> tmp;
    for (unsigned i = 0; i < size(); ++i) {
      if (get(i)) {
        tmp.push_back(get(i)->deep_copy());
      } else {
        tmp.push_back(nullptr);
      }
    }
    return new MvType(loc(), std::move(tmp));
  }

  Sexpression *cast(Expression *rval) const override;

  Sexpression *default_initializer_value() const override;
};

class InitializerType final : public priv::CompositeType {
public:
  InitializerType(origin_t loc, std::vector<const Type *> &&t)
      : CompositeType(loc, idOf(this), std::move(t)) {}
  ~InitializerType() {}

  Type *deep_copy() const override {

    std::vector<const Type *> tmp;
    for (unsigned i = 0; i < size(); ++i) {
      if (get(i)) {
        tmp.push_back(get(i)->deep_copy());
      } else {
        tmp.push_back(nullptr);
      }
    }
    return new InitializerType(loc(), std::move(tmp));
  }

  Sexpression *default_initializer_value() const override { UNREACHABLE(); }
};

// Type used to recover from error during the type pass.
class ErrorType final : public Type {
public:
  ErrorType() : Type(Location::builtin(), idOf(this)) {}
  ~ErrorType() {}

  Type *deep_copy() const override { return new ErrorType(*this); }

  void display(std::ostream &os = std::cout) const override {
    os << "error_type";
  }
  void displayVarType(std::ostream &os = std::cout) const override {
    Type::displayVarType(os);
  }
  void displayVarName(const char *name,
                      std::ostream &os = std::cout) const override {
    Type::displayVarName(name, os);
  }

  void makeDef([[maybe_unused]] const char *name,
               std::ostream &os = std::cout) const override {
    Type::makeDef(name, os);
  }

  Sexpression *cast(Expression *rval) const override {
    return Type::cast(rval);
  }

  unsigned ACL2ValWidth() const override { return Type::ACL2ValWidth(); }

  bool isEqual([[maybe_unused]] const Type *other) const override {
    return true;
  }
  bool
  canBeImplicitlyCastTo([[maybe_unused]] const Type *target) const override {
    return true;
  }

  Sexpression *default_initializer_value() const override {
    return new Symbol("ErrorTypeValue");
  }
};

inline bool isIntegerType(const Type *t) {
  return dynamic_cast<const PrimType *>(t) ||
         dynamic_cast<const IntType *>(t) || dynamic_cast<const EnumType *>(t);
}

#endif // TYPES_H
