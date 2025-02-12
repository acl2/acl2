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
  virtual Sexpression *cast(Expression *rval) const;

  // TODO refactore.
  // overridden by IntType
  virtual unsigned ACL2ValWidth() const {

    // Boundary on the width of the value of an object of this type.
    // Used to avoid unnecessary call to bits.
    return 0;
  }

  virtual bool isEqual(const Type *other) const = 0;
  virtual bool canBeImplicitlyCastTo(const Type *target) const = 0;

  virtual Sexpression *eval(Sexpression *sexpr) const { return sexpr; }

  origin_t &loc() { return origin_; }
  const origin_t &loc() const { return origin_; }

  origin_t origin_;

  NodesId id() const { return id_; }

  void setConst() { isConst_ = true; }
  bool isConst() const { return isConst_; }

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

  virtual PrimType *deep_copy() const { return new PrimType(*this); }

  static PrimType Bool() {
    return PrimType(Location::dummy(), "bool", nullptr, Rank::Bool, false);
  }
  static PrimType Int() {
    return PrimType(Location::dummy(), "int", nullptr, Rank::Int, true);
  }
  static PrimType Uint() {
    return PrimType(Location::dummy(), "uint", nullptr, Rank::Int, false);
  }
  static PrimType Int64() {
    return PrimType(Location::dummy(), "int64", "int64", Rank::Long, true);
  }
  static PrimType Uint64() {
    return PrimType(Location::dummy(), "uint64", "uint64", Rank::Long, false);
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

  const std::optional<std::string> RACname_;
  Rank rank_;
  bool signed_;
};

extern PrimType boolType;
extern PrimType intType;
extern PrimType uintType;
extern PrimType int64Type;
extern PrimType uint64Type;

class DefinedType : public Symbol, public Type {
public:
  DefinedType(origin_t loc, const char *s, Type *t)
      : Symbol(s), Type(loc, idOf(this)), def_(t) {}

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

  unsigned ACL2ValWidth() const override {
    return derefType()->ACL2ValWidth();
  }

  void displayDef(std::ostream &os = std::cout) const {
    def_->makeDef(getname(), os);
  }

  Type *getdef() { return def_; }
  const Type *getdef() const { return def_; }

  Type *derefType() const {

    Type *t = def_;
    t->origin_ = this;

    while (auto *dt = dynamic_cast<DefinedType *>(t)) {
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

private:
  Type *def_;
};

class IntType final : public Type {
public:
  IntType(origin_t loc, Expression *w, Expression *s)
      : Type(loc, idOf(this)), width_(w), isSigned_(s) {}

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

private:
  Expression *width_;
  Expression *isSigned_;
};

class ArrayType : public Type {
public:
  Type *baseType;
  Expression *dim;

  ArrayType(origin_t loc, Expression *d, Type *t)
      : Type(loc, idOf(this)), baseType(t), dim(d) {}

  Type *getBaseType() { return baseType; }
  const Type *getBaseType() const { return baseType; }

  void display(std::ostream &os) const override;
  void displayVarType(std::ostream &os = std::cout) const override;
  void displayVarName(const char *name,
                      std::ostream &os = std::cout) const override;
  void makeDef(const char *name, std::ostream &os) const override;

  bool isEqual(const Type *other) const override;

  bool canBeImplicitlyCastTo([
      [maybe_unused]] const Type *target) const override {
    return false;
  }

  inline void setSTDArray() { isSTDarray_ = true; }
  inline bool isSTDArray() const { return isSTDarray_; }

private:
  bool isSTDarray_ = false;
};

class StructField {
public:
  Symbol *sym;
  Type *type;
  StructField(Type *t, char *n);
  const char *getname() const { return sym->getname(); }
  void display(std::ostream &os, unsigned indent = 0) const;

  bool operator==(const StructField &other) const {
    return strcmp(sym->getname(), other.getname())
           && type->isEqual(other.type);
  }
};

class StructType : public Type {
public:
  StructType(origin_t loc, std::vector<StructField *> f);

  void displayFields(std::ostream &os) const;
  void display(std::ostream &os) const override;
  void makeDef(const char *name, std::ostream &os = std::cout) const override;

  const std::vector<StructField *> &fields() const { return fields_; }

  const StructField *getField(const std::string &name) const;

  bool isEqual(const Type *) const override;

  bool canBeImplicitlyCastTo([
      [maybe_unused]] const Type *target) const override {
    return false;
  }

private:
  std::vector<StructField *> fields_;
};

class EnumType : public PrimType {
public:
  EnumType(origin_t loc, std::vector<EnumConstDec *> v);

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

  const std::vector<EnumConstDec *> &values() { return vals_; }

private:
  std::vector<EnumConstDec *> vals_;
};

namespace priv {
  class CompositeType : public Type {
  public:
    CompositeType(origin_t loc, NodesId id, std::vector<Type *> &&t)
        : Type(loc, id), types_(t) {}

    void display(std::ostream &os) const override;

    unsigned size() const { return types_.size(); }
    const Type *get(unsigned n) const { return types_[n]; }
    const Type *get(unsigned n) { return types_[n]; }
    const std::vector<Type *> &types() const { return types_; }

    bool isEqual(const Type *other) const override;

    bool canBeImplicitlyCastTo([
        [maybe_unused]] const Type *target) const override {
      return false;
    }

  private:
    std::vector<Type *> types_;
  };
}

class MvType final : public priv::CompositeType {
public:
  MvType(origin_t loc, std::vector<Type *> &&t)
      : CompositeType(loc, idOf(this), std::move(t)) {}
};

class InitializerType final : public priv::CompositeType {
public:
  InitializerType(origin_t loc, std::vector<Type *> &&t)
      : CompositeType(loc, idOf(this), std::move(t)) {}
};

// Type used to recover from error during the type pass.
class ErrorType final : public Type {
public:
  ErrorType() : Type(Location::dummy(), idOf(this)) {}

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
  bool canBeImplicitlyCastTo([
      [maybe_unused]] const Type *target) const override {
    return true;
  }
};

inline bool isIntegerType(const Type *t) {
  return dynamic_cast<const PrimType *>(t) || dynamic_cast<const IntType *>(t)
         || dynamic_cast<const EnumType *>(t);
}

#endif // TYPES_H
