#ifndef STATEMENTS_H
#define STATEMENTS_H

#include "expressions.h"
#include "types.h"
#include "utils.h"

using namespace std;

//***********************************************************************************
// Statements
//***********************************************************************************

class Block;
class FunCall;
class TempCall;

class Statement
{
public:
  virtual void display (ostream &os, unsigned indent = 0) = 0;
  virtual void displayAsRightBranch (ostream &os, unsigned indent = 0);
  virtual void displayWithinBlock (ostream &os, unsigned indent = 0);
  virtual Block *blockify ();
  virtual Block *blockify (Statement *s);
  virtual Statement *subst (SymRef *var, Expression *expr);
  virtual Sexpression *ACL2Expr () = 0;
  virtual void noteReturnType (Type *t);
  virtual void markAssertions (FunDef *f);
};

class SimpleStatement : public Statement
{
public:
  SimpleStatement ();
  void display (ostream &os, unsigned indent = 0) override;
  virtual void displaySimple (ostream &os) = 0;
};

class SymDec
{
public:
  Symbol *sym;
  Type *type;
  Expression *init;
  SymDec (const char *n, Type *t, Expression *i = nullptr);
  const char *
  getname () const
  {
    return sym->getname ();
  }
  void displaySymDec (ostream &os) const;
  virtual bool isGlobal ();
  virtual bool isROM ();
  virtual bool isConst ();
  virtual int evalConst ();
  virtual Sexpression *ACL2SymExpr ();
};

class EnumConstDec : public SymDec
{
public:
  EnumConstDec (const char *n, Expression *v = nullptr);
  void display (ostream &os) const;
  bool isConst ();
  // ACL2expr Weird
  Sexpression *ACL2Expr ();
  Sexpression *ACL2SymExpr ();
};

class VarDec : public SimpleStatement, public SymDec
{
public:
  VarDec (const char *n, Type *t, Expression *i = nullptr);
  void displaySimple (ostream &os) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  Sexpression *ACL2SymExpr () override;
};

class ConstDec : public VarDec
{
public:
  ConstDec (const char *n, Type *t, Expression *i);
  void displaySimple (ostream &os) override;
  Statement *subst (SymRef *var, Expression *val) override;
  bool isConst () override;
  bool isGlobal () override;
  bool isROM () override;
  Sexpression *ACL2SymExpr () override;
};

class MulVarDec : public SimpleStatement
{
public:
  List<VarDec> *decs;
  MulVarDec (VarDec *dec1, VarDec *dec2);
  MulVarDec (List<VarDec> *decs);
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void displaySimple (ostream &os) override;
};

class MulConstDec : public SimpleStatement
{
public:
  List<ConstDec> *decs;
  MulConstDec (ConstDec *dec1, ConstDec *dec2);
  MulConstDec (List<ConstDec> *decs);
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void displaySimple (ostream &os) override;
};

class TempParamDec : public SymDec
{
public:
  TempParamDec (const char *n, Type *t);
  bool isConst () override;
  Sexpression *ACL2SymExpr () override;
};

class BreakStmt : public SimpleStatement
{
public:
  BreakStmt ();
  void displaySimple (ostream &os) override;
  Sexpression *ACL2Expr () override;
};

class ReturnStmt : public SimpleStatement
{
public:
  Expression *value;
  Type *returnType;
  ReturnStmt (Expression *v);
  void displaySimple (ostream &os) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void noteReturnType (Type *t) override;
};

class NullStmt : public SimpleStatement
{
public:
  NullStmt ();
  void displaySimple (ostream &os) override;
  Sexpression *ACL2Expr () override;
};

class Assertion : public SimpleStatement
{
public:
  Expression *expr;
  FunDef *funDef;
  Assertion (Expression *e);
  void displaySimple (ostream &os) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void markAssertions (FunDef *f) override;
};

class Assignment : public SimpleStatement
{
public:
  Expression *lval;
  const char *op;
  Expression *rval;
  Assignment (Expression *l, const char *o, Expression *r = nullptr);
  void displaySimple (ostream &os) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
};

class AssignBit : public SimpleStatement
{
public:
  Expression *base;
  Expression *index;
  Expression *val;
  AssignBit (Expression *b, Expression *i, Expression *v);
  void displaySimple (ostream &os) override;
};

class AssignRange : public SimpleStatement
{
public:
  Expression *base;
  Expression *high;
  Expression *low;
  Expression *width;
  Expression *val;
  AssignRange (Expression *b, Expression *h, Expression *l, Expression *w,
               Expression *v);
  void displaySimple (ostream &os) override;
};

class AssignFull : public SimpleStatement
{
public:
  Expression *base;
  unsigned width;
  Expression *val;
  AssignFull (Expression *b, unsigned w, Expression *v);
  void displaySimple (ostream &os) override;
};

class MultipleAssignment : public SimpleStatement
{
  std::vector<Expression *> lval;
  FunCall *rval;

public:
  MultipleAssignment (FunCall *r, std::vector<Expression *> e);
  void displaySimple (ostream &os) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
};

class Block : public Statement
{
public:
  List<Statement> *stmtList;
  Block (List<Statement> *s);
  Block (Statement *s);
  Block (Statement *s1, Statement *s2);
  Block (Statement *s1, Statement *s2, Statement *s3);
  Block *blockify () override;
  Block *blockify (Statement *s) override;
  void display (ostream &os, unsigned indent = 0) override;
  void displayWithinBlock (ostream &os, unsigned indent = 0) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void noteReturnType (Type *t) override;
  void markAssertions (FunDef *f) override;
};

class IfStmt : public Statement
{
public:
  Expression *test;
  Statement *left;
  Statement *right;
  IfStmt (Expression *t, Statement *l, Statement *r);
  void display (ostream &os, unsigned indent = 0) override;
  void displayAsRightBranch (ostream &os, unsigned indent = 0) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void markAssertions (FunDef *f) override;
  void noteReturnType (Type *t) override;
};

class ForStmt : public Statement
{
public:
  SimpleStatement *init;
  Expression *test;
  Assignment *update;
  Statement *body;
  ForStmt (SimpleStatement *v, Expression *t, Assignment *u, Statement *b);
  void display (ostream &os, unsigned indent = 0) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void markAssertions (FunDef *f) override;
};

// Why not part of hierarchy ? inherit form statement ?
class Case
{
public:
  Expression *label;
  List<Statement> *action;
  Case (Expression *l, List<Statement> *a);
  void display (ostream &os, unsigned indent = 0);
  Case *subst (SymRef *var, Expression *val);
  void markAssertions (FunDef *f);
};

class SwitchStmt : public Statement
{
  Expression *test;
  BetterList<Case> cases;

public:
  SwitchStmt (Expression *t, List<Case> *c);
  void display (ostream &os, unsigned indent = 0) override;
  Statement *subst (SymRef *var, Expression *val) override;
  Sexpression *ACL2Expr () override;
  void markAssertions (FunDef *f) override;
};

#endif // STATEMENTS_H
