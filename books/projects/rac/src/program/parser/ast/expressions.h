#ifndef EXPRESSIONS_H
#define EXPRESSIONS_H

#include "../../sexpressions.h"
#include "../utils/diagnostics.h"
#include "../utils/utils.h"
#include "fwd.h"
#include "nodesid.h"

//***********************************************************************************
// Expressions
//***********************************************************************************

class Expression {
public:
  Expression(NodesId id, Location loc) : id_(id), loc_(loc){};

  virtual bool isStaticallyEvaluable();
  virtual int evalConst();

  virtual bool isInteger();

  const Type *get_type() const { return t_; }
  const Type *get_type() { return t_; }

  virtual void display(std::ostream &os) const = 0;

  // The following method converts an expression to an S-expression.
  virtual Sexpression *ACL2Expr() = 0;
  virtual Sexpression *ACL2Assign(Sexpression *rval);

  unsigned ACL2ValWidth();

  inline NodesId id() const { return id_; }
  inline const Location &loc() { return loc_; }

  // Only during the type passs we are allowed to modify the type.
  void set_type(const Type *t) { t_ = t; }

private:
  // The type of the expression. Null means not yet typed, but after the type
  // pass, it should be always set with a concrete type (not a typedef).
  const Type *t_ = nullptr;

protected:
  const NodesId id_;
  const Location loc_;
};

class Constant : public Expression {
public:
  Constant(NodesId id, Location loc, const char *n);
  Constant(NodesId id, Location loc, std::string &&n);

  bool isStaticallyEvaluable() override;
  bool isInteger() override { return true; }

  Sexpression *ACL2Expr() override;

  const char *getname() const { return name_.c_str(); }

  // Check is the value can fit inside a bit vector.
  virtual bool fitInside(bool sign, unsigned width) const = 0;

protected:
  std::string name_;
};

class Integer final : public Constant {
public:
  Integer(Location loc, const char *n);
  Integer(Location loc, BigInt n, const std::string &suffix = "");

  // TODO if it is an uint/int64/uint64 this could overflow.
  int evalConst() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;

  bool fitInside(bool sign, unsigned width) const override {
    return val_.can_fit_inside(sign, width);
  }

  static Integer *zero_v(Location loc) { return new Integer(loc, "0"); }
  static Integer *one_v(Location loc) { return new Integer(loc, "1"); }
  static Integer *two_v(Location loc) { return new Integer(loc, "2"); }

  enum Format { Binary, Decimal, Hexadecimal };
  Format format() const {

    if (!strncmp(getname(), "0x", 2)) {
      return Format::Hexadecimal;
    } else if (!strncmp(getname(), "-0x", 3)) {
      return Format::Hexadecimal;
    } else if (!strncmp(getname(), "0b", 2)) {
      return Format::Binary;
    } else if (!strncmp(getname(), "-0b", 3)) {
      return Format::Binary;
    } else {
      return Format::Decimal;
    }
  }

  bool has_suffix_unsigned() const {
    for (char c : suffix_) {
      if (c == 'U' || c == 'u') {
        return true;
      }
    }
    return false;
  }

  // We consider long means 64 bits. When we use slec, long is 32 bits and long
  // long 64.
  bool has_suffix_long() const {
    bool more_than_one = false;
    for (char c : suffix_) {
      if (c == 'L' || c == 'l') {
        if (more_than_one)
          return true;
        else
          more_than_one = true;
      }
    }
    return false;
  }

  BigInt val_;
  std::string suffix_;
};

class Boolean final : public Constant {
  // PrimType (boolType)
public:
  Boolean(Location loc, bool value);
  int evalConst() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;

  bool fitInside([[maybe_unused]] bool sign, unsigned width) const override {
    // Is this really necessary ? A integer with 0 bit should not be valid
    // anyway...
    return width > 0;
  }

  static Boolean *true_v(Location loc) { return new Boolean(loc, true); }
  static Boolean *false_v(Location loc) { return new Boolean(loc, false); }

private:
  bool value_;
};

class Parenthesis final : public Expression {
public:
  Parenthesis(Location loc, Expression *e)
      : Expression(idOf(this), loc), expr_(e) {
    assert(e);
  }

  bool isStaticallyEvaluable() override {
    return expr_->isStaticallyEvaluable();
  }
  int evalConst() override { return expr_->evalConst(); }
  bool isInteger() override { return expr_->isInteger(); }

  // TODO rename
  void display(std::ostream &os) const override {
    os << '(';
    expr_->display(os);
    os << ')';
  }

  virtual Sexpression *ACL2Expr() override { return expr_->ACL2Expr(); }
  virtual Sexpression *ACL2Assign(Sexpression *rval) override {
    return expr_->ACL2Assign(rval);
  }

  Expression *expr_;
};

class SymRef final : public Expression {
public:
  SymRef(Location loc, SymDec *s);
  virtual bool isStaticallyEvaluable() override;
  virtual int evalConst() override;
  bool isInteger() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;
  Sexpression *ACL2Assign(Sexpression *rval) override;

  SymDec *symDec;
};

class FunCall : public Expression {
  // type: rtype
public:
  FunDef *func;
  std::vector<Expression *> args;
  FunCall(Location loc, FunDef *f, std::vector<Expression *> &&a);
  FunCall(NodesId id, Location loc, FunDef *f, std::vector<Expression *> &&a);

  bool isInteger() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;
};

class TempCall final : public FunCall {
public:
  Symbol *instanceSym;
  std::vector<Expression *> params;
  TempCall(Location loc, Template *f, std::vector<Expression *> &&a,
           std::vector<Expression *> &&p);
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;
};

class Initializer final : public Expression {
public:
  std::vector<Expression *> vals;
  Initializer(Location loc, std::vector<Expression *> v);
  void display(std::ostream &os) const override;

  // Initializer does not make sense on their own: they must be cast to an
  // actual type.
  Sexpression *ACL2Expr() override { UNREACHABLE(); }

  Sexpression *ACL2ArrayExpr(const ArrayType *t, bool output_optmized_const);
  Sexpression *ACL2TupleExpr(const MvType *t);
  Sexpression *ACL2StructExpr(const StructType *t);
};

class ArrayRef final : public Expression {
public:
  Expression *array;
  Expression *index;
  ArrayRef(Location loc, Expression *a, Expression *i);

  bool isInteger() override;
  void display(std::ostream &os) const override;

  Sexpression *ACL2Expr() override;
  Sexpression *ACL2Assign(Sexpression *rval) override;
};

class StructRef final : public Expression {
public:
  Expression *base;
  char *field;
  StructRef(Location loc, Expression *s, char *f);
  bool isInteger() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;
  Sexpression *ACL2Assign(Sexpression *rval) override;
};

class Subrange final : public Expression {
public:
  Expression *base;
  Expression *high;
  Expression *low;

  Expression *width() { return width_; }

  Subrange(Location loc, Expression *b, Expression *l, Expression *w);

  bool isInteger() override { return true; }
  void display(std::ostream &os) const override;

  Sexpression *ACL2Expr() override;
  Sexpression *ACL2Assign(Sexpression *rval) override;

private:
  Expression *width_;
};

class PrefixExpr final : public Expression {
public:
  enum class Op {
#define APPLY_BINARY_OP(_, __)
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(NAME, __) NAME,
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  };

  Expression *expr;
  Op op;

  static Op parseOp(const char *o);

  PrefixExpr(Location loc, Expression *e, Op o);
  bool isStaticallyEvaluable() override;
  int evalConst() override;
  bool isInteger() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;
};

std::ostream &operator<<(std::ostream &os, PrefixExpr::Op op);
std::string to_string(PrefixExpr::Op op);

class CastExpr final : public Expression {
public:
  Expression *expr;
  const Type *type;

  CastExpr(Location loc, Expression *e, const Type *t)
    : Expression(idOf(this), loc)
    , expr(e)
    , type(t)
  {}

  bool isStaticallyEvaluable() override { return expr->isStaticallyEvaluable(); }

  int evalConst() override { return expr->evalConst(); }

  bool isInteger() override { return expr->isInteger(); }

  void display(std::ostream &os) const override { expr->display(os); }

  Sexpression *ACL2Expr() override;
};

class BinaryExpr final : public Expression {
public:
  enum class Op {
#define APPLY_BINARY_OP(NAME, _) NAME,
#define APPLY_ASSIGN_OP(_, __)
#define APPLY_UNARY_OP(_, __)
#include "operators.def"
#undef APPLY_BINARY_OP
#undef APPLY_ASSIGN_OP
#undef APPLY_UNARY_OP
  };

  Expression *expr1;
  Expression *expr2;
  Op op;

  BinaryExpr(Location loc, Expression *e1, Expression *e2, Op o);

  bool isStaticallyEvaluable() override;
  int evalConst() override;
  bool isInteger() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;

  static bool isOpShift(Op o);
  static bool isOpArithmetic(Op o);
  static bool isOpBitwise(Op o);
  static bool isOpCompare(Op o);
  static bool isOpLogical(Op o);

  static Op parseOp(const char *o);
};

std::ostream &operator<<(std::ostream &os, BinaryExpr::Op op);
std::string to_string(BinaryExpr::Op op);

class CondExpr final : public Expression {
public:
  Expression *expr1;
  Expression *expr2;
  Expression *test;
  CondExpr(Location loc, Expression *e1, Expression *e2, Expression *t);
  bool isInteger() override;
  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;

  int evalConst() override;
  bool isStaticallyEvaluable() override {
    return expr1->isStaticallyEvaluable() && expr2->isStaticallyEvaluable() &&
           test->isStaticallyEvaluable();
  }
};

class MultipleValue final : public Expression {
public:
  MultipleValue(Location loc, const MvType *t, std::vector<Expression *> &&e);

  void display(std::ostream &os) const override;
  Sexpression *ACL2Expr() override;
  const std::vector<Expression *> &expr() const { return expr_; }

private:
  std::vector<Expression *> expr_;
};

#endif // EXPRESSIONS_H
