#ifndef STATEMENTS_H
#define STATEMENTS_H

#include "fwd.h"
#include "nodesid.h"
#include "types.h"

#include "../../sexpressions.h"
#include "../utils/diagnostics.h"
#include "../utils/utils.h"

//***********************************************************************************
// Statements
//***********************************************************************************

class Statement {
public:
  Statement(NodesId id, Location loc) : id_(id), loc_(loc) {}

  virtual void display(std::ostream &os, unsigned indent = 0) = 0;
  virtual void displayAsRightBranch(std::ostream &os, unsigned indent = 0);
  virtual void displayWithinBlock(std::ostream &os, unsigned indent = 0);
  virtual Block *blockify();
  virtual Block *blockify(Statement *s);
  virtual Sexpression *ACL2Expr() = 0;

  inline NodesId id() const { return id_; }
  inline const Location &loc() const { return loc_; }

private:
  const NodesId id_;

protected:
  Location loc_;
};

class SimpleStatement : public Statement {
public:
  SimpleStatement(NodesId id, Location loc) : Statement(id, loc) {}
  void display(std::ostream &os, unsigned indent = 0) override;
  virtual void displaySimple(std::ostream &os) = 0;
};

class SymDec : public SimpleStatement {
public:
  // TODO
  Symbol *sym;

  Expression *init;
  SymDec(NodesId id, Location loc, const char *n, Type *t,
         Expression *i = nullptr);

  const char *getname() const { return sym->getname(); }
  virtual void displaySymDec(std::ostream &os) const;
  virtual bool isGlobal() const { return false; }

  Type *get_type() const { return type_; }
  void set_type(Type *t) {
    type_ = t;
    if (!original_type_) {
      original_type_ = t;
    }
  }
  Type *get_original_type() { return original_type_; }

  virtual bool isStaticallyEvaluable();
  int evalConst();

  virtual Sexpression *ACL2SymExpr();

private:
  Type *type_;
  // Used to report the error with the original typedef (type will be
  // dereferenced later).
  Type *original_type_;
};

class EnumConstDec final : public SymDec {
public:
  EnumConstDec(Location loc, const char *n, Expression *v = nullptr);
  // TODO indent.
  void display(std::ostream &os, unsigned) override;
  void displaySimple(std::ostream &os) override { display(os, 0); }
  bool isStaticallyEvaluable() override;

  Sexpression *ACL2Expr() override;
  Sexpression *ACL2SymExpr() override;
};

class VarDec : public SymDec {
public:
  VarDec(Location loc, const char *n, Type *t, Expression *i = nullptr);
  VarDec(NodesId id, Location loc, const char *n, Type *t,
         Expression *i = nullptr);
  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;
  Sexpression *ACL2SymExpr() override;


  bool isStaticallyEvaluable() const {
    return get_type()->isConst() && isIntegerType(get_type());
  }

  void setGlobal() { isGlobal_ = true; }
  bool isGlobal() const override { return isGlobal_; }


private:
  bool isGlobal_ = false;
};

class MulVarDec : public SimpleStatement {
public:
  std::vector<VarDec *> decs;
  MulVarDec(Location loc, VarDec *dec1, VarDec *dec2);
  MulVarDec(Location loc, std::vector<VarDec *> &&decs);
  Sexpression *ACL2Expr() override;
  void displaySimple(std::ostream &os) override;
};

class TempParamDec final : public SymDec {
public:
  TempParamDec(Location loc, const char *n, Type *t);
  bool isStaticallyEvaluable() override;
  Sexpression *ACL2SymExpr() override;

  // TODO
  void display(std::ostream &, unsigned) override{};
  void displaySimple(std::ostream &) override{};

  Sexpression *ACL2Expr() override {
    assert(false);
    return nullptr;
  }
};

class BreakStmt final : public SimpleStatement {
public:
  BreakStmt(Location loc);
  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;
};

class ReturnStmt final : public SimpleStatement {
public:
  Expression *value;
  Type *returnType = nullptr;
  ReturnStmt(Location loc, Expression *v);
  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;
};

class NullStmt final : public SimpleStatement {
public:
  NullStmt(Location loc);
  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;
};

class Assertion final : public SimpleStatement {
public:
  Expression *expr;
  FunDef *funDef;
  Assertion(Location loc, Expression *e);
  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;
};

class Assignment final : public SimpleStatement {
public:
  Expression *lval;
  const char *op;
  Expression *rval;
  Expression *index = nullptr;

  Assignment(Location loc, Expression *l, const char *o, Expression *r);
  Assignment(Location loc, Expression *l, Expression *r, Expression *i)
      : SimpleStatement(idOf(this), loc), lval(l), op("set_slc"), rval(r),
        index(i) {}

  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;

  void resolveOverload();
  void desugar();
};

class MultipleAssignment : public SimpleStatement {
  std::vector<Expression *> lval_;
  FunCall *rval_;

public:
  MultipleAssignment(Location loc, FunCall *r, std::vector<Expression *> e);
  void displaySimple(std::ostream &os) override;
  Sexpression *ACL2Expr() override;

  const std::vector<Expression *> &lvals() const { return lval_; }
  FunCall *rval() { return rval_; }
};

class Block final : public Statement {
public:
  std::vector<Statement *> stmtList;

  Block(Location loc, std::vector<Statement *> &&s);
  Block(Location loc, Statement *s);
  Block(Location loc, Statement *s1, Statement *s2);

  Block *blockify() override;
  Block *blockify(Statement *s) override;
  void display(std::ostream &os, unsigned indent = 0) override;
  void displayWithinBlock(std::ostream &os, unsigned indent = 0) override;
  Sexpression *ACL2Expr() override;
};

class IfStmt final : public Statement {
public:
  Expression *test;
  Statement *left;
  Statement *right;
  IfStmt(Location loc, Expression *t, Statement *l, Statement *r);
  void display(std::ostream &os, unsigned indent = 0) override;
  void displayAsRightBranch(std::ostream &os, unsigned indent = 0) override;
  Sexpression *ACL2Expr() override;
};

class ForStmt final : public Statement {
public:
  SimpleStatement *init;
  Expression *test;
  Assignment *update;
  Statement *body;

  ForStmt(Location loc, SimpleStatement *v, Expression *t, Assignment *u,
          Statement *b);
  void display(std::ostream &os, unsigned indent = 0) override;
  Sexpression *ACL2Expr() override;
};

class Case final : public Statement {
public:
  Case(Location loc, Expression *l, std::vector<Statement *> &&a);
  void display(std::ostream &os, unsigned indent = 0) override;

  bool isDefaultCase() const { return label == nullptr; }
  bool isFallthrough() const { return action.size() == 0; }

  Sexpression *ACL2Expr() override { UNREACHABLE(); }

  Expression *label;
  std::vector<Statement *> action;
};

class SwitchStmt : public Statement {
public:
  SwitchStmt(Location loc, Expression *t, std::vector<Case *> c);
  void display(std::ostream &os, unsigned indent = 0) override;
  Sexpression *ACL2Expr() override;

  Expression *test() { return test_; }
  const std::vector<Case *> &cases() { return cases_; }

private:
  Expression *test_;
  std::vector<Case *> cases_;
};

#endif // STATEMENTS_H
