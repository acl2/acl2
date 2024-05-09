#ifndef TYPES_H
#define TYPES_H

#include "parser.h"
#include "utils.h"

using namespace std;

//***********************************************************************************
// Types
//***********************************************************************************

class Expression;
class SymRef;
class EnumConstDec;

// Derived classes:
//
//   PrimType           (primitive type: uintTYpe, intType, boolType)
//   DefinedType        (introduced by typedef)
//   RegType            (Algorithmic C register type)
//   UintType           (unsigned limited integer register)
//   IntType            (signed limited integer register)
//   FPType             (fixed-point register
//   UfixedType         (unsigned fixed-point register
//   FixedType          (signed fixed-point register
//   ArrayType          (array type)
//   StructType         (struct type) EnumType (enumeration type)
//   MvType             (multiple value type)
class Type {
public:
  // overridden by PrimType
  virtual bool isPrimType() const { return false; }
  // overridden by RegType
  virtual bool isRegType() const { return false; }
  // overridden by FPType
  virtual bool isArrayType() const { return false; }
  // overridden by ArrayType
  virtual bool isStructType() const { return false; }
  // overridden by StructType
  virtual bool isIntegerType() const { return false; }
  // overridden by EnumType
  virtual bool isFPType() const { return false; }
  // overridden by integer types
  virtual bool isEnumType() const { return false; }
  // overridden by DefinedType
  virtual Type *derefType() { return this; }
  virtual void display(ostream &os = cout) const = 0;

  virtual void displayVarType(ostream &os = cout) const {
    // How this type is displayed in a variable declaration
    display(os);
  }

  // overridden by ArrayType
  virtual void displayVarName([[maybe_unused]] const char *name,
                              ostream &os = cout) const {
    // How a variable of this type is displayed in a variable declaration
    display(os);
  }

  // overridden by ArrayType, StructType, and EnumType
  virtual void makeDef([[maybe_unused]] const char *name, ostream &os = cout) {
    // How this type is displayed in a type definition.
    os << "\ntypedef ";
    display(os);
    os << " " << name << ";";
  }

  // TODO this line depends on Expression which is defined below. For now, the
  // implementation stays in output.c.
  // overridden by RegType
  virtual Sexpression *ACL2Assign(Expression *rval);
  //  {
  //    // Convert rval to an S-expression to be assigned to an object of this
  //    type. return rval->ACL2Expr()
  //  }

  // overridden by UintType
  virtual unsigned ACL2ValWidth() {
    // TODO: shady, we should probably have something to express unbounded,
    // unknown and zero (imagine a case were translate an unknown size value
    // like it was unbounded...)
    //
    // Boundary on the width of the value of an object of this type.
    // 0 indicates unknown or unbounded width.
    // Used to avoid unnecessary call to bits.
    return 0;
  }

  // overridden by RegType
  virtual Sexpression *ACL2Eval(Sexpression *s) {
    // For a RegType, the numerical value represented by a given bit vector s.
    // For any other type, just return s.
    return s;
  }
};

class PrimType : public Symbol, public Type {
public:
  PrimType(const char *s, const char *m = nullptr)
      : Symbol(s), RACname_(m ? std::optional(std::string(m)) : nullopt) {}

  bool isPrimType() const override { return true; }
  bool isIntegerType() const override { return true; }

  void display(ostream &os) const override {
    if (RACname_) {
      os << *RACname_;
    } else {
      Symbol::display(os);
    }
  }

private:
  const std::optional<std::string> RACname_;
};

extern PrimType boolType;
extern PrimType intType;
extern PrimType uintType;
extern PrimType int64Type;
extern PrimType uint64Type;

class DefinedType : public Symbol, public Type {
public:
  DefinedType(const char *s, Type *t) : Symbol(s), def_(t) {}

  void display(ostream &os) const { Symbol::display(os); }

  void displayDef(ostream &os = cout) const {
    if (!(def_->isRegType())) {
      def_->makeDef(getname(), os);
    }
  }

  Type *getdef() { return def_; }
  Type *&getdef_mutref() { return def_; }
  Type *derefType() { return def_->derefType(); }

private:
  Type *def_;
};

class RegType : public Type {
public:
  RegType(Expression *w) : width_(w) {}

  Expression *width() const { return width_; }

  bool isRegType() const override { return true; }
  Sexpression *ACL2Assign(Expression *rval) override;

private:
  Expression *width_;
};

class UintType : public RegType {
public:
  UintType(Expression *w) : RegType(w) {}

  bool isIntegerType() const override { return true; }
  void display(ostream &os = cout) const override;
  unsigned ACL2ValWidth() override;
};

class IntType : public RegType {
public:
  IntType(Expression *w) : RegType(w) {}
  bool isIntegerType() const override { return true; }
  void display(ostream &os = cout) const override;
  Sexpression *ACL2Eval(Sexpression *s) override;
};

class FPType : public RegType {
public:
  Expression *iwidth;
  FPType(Expression *w, Expression *iw);
  bool isFPType() const override { return true; }
  Sexpression *ACL2Assign(Expression *rval) override;
};

class UfixedType : public FPType {
public:
  UfixedType(Expression *w, Expression *iw);
  void display(ostream &os = cout) const;
  Sexpression *ACL2Eval(Sexpression *s);
};

class FixedType : public FPType {
public:
  bool isSigned();
  FixedType(Expression *w, Expression *iw);
  void display(ostream &os = cout) const;
  Sexpression *ACL2Eval(Sexpression *s);
};

class ArrayType : public Type {
public:
  Type *baseType;
  Expression *dim;

  ArrayType(Expression *d, Type *t) : baseType(t), dim(d) {}

  Type *getBaseType();
  bool isArrayType() const override { return true; }
  void display(ostream &os) const override;
  void displayVarType(ostream &os = cout) const override;
  void displayVarName(const char *name, ostream &os = cout) const override;
  void makeDef(const char *name, ostream &os) override;
};

class StructField {
public:
  Symbol *sym;
  Type *type;
  StructField(Type *t, char *n);
  const char *getname() const { return sym->getname(); }
  void display(ostream &os, unsigned indent = 0) const;
};

class StructType : public Type {
public:
  List<StructField> *fields;
  StructType(List<StructField> *f);
  bool isStructType() const override { return true; }
  void displayFields(ostream &os) const;
  void display(ostream &os) const override;
  void makeDef(const char *name, ostream &os = cout) override;
};

class EnumType : public Type {
public:
  List<EnumConstDec> *vals;
  EnumType(List<EnumConstDec> *v);
  bool isEnumType() const override { return true; }
  bool isIntegerType() const override { return true; }
  void displayConsts(ostream &os) const;
  void display(ostream &os) const override;
  void makeDef(const char *name, ostream &os = cout) override;
  // ACL2expr Weird
  Sexpression *ACL2Expr();
  Sexpression *getEnumVal(Symbol *s);
};

class MvType : public Type {
public:
  std::vector<Type *> type;
  MvType(std::initializer_list<Type *> &&t) : type(t) {}
  void display(ostream &os) const;
};

#endif // TYPES_H
