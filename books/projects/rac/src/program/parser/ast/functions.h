#ifndef FUNCTIONS_H
#define FUNCTIONS_H

#include "fwd.h"
#include "nodesid.h"
#include "statements.h"

//***********************************************************************************
// Functions
//***********************************************************************************

class FunDef : public Statement {

public:
  FunDef(Location loc, std::string name, const Type *returnType,
         std::vector<VarDec *> p, Block *b);
  FunDef(NodesId id, Location loc, std::string name, const Type *returnType,
         std::vector<VarDec *> p, Block *b);

  const char *getname() const { return name_.c_str(); }

  const Type *returnType() const { return returnType_; }
  const std::vector<VarDec *> &params() const { return params_; }
  Block *body() const { return body_; }

  void display(std::ostream &os, unsigned indent) override;
  Sexpression *ACL2Expr() override;

protected:
  std::string name_;
  const Type *returnType_;
  std::vector<VarDec *> params_;
  Block *body_;

private:
  void displayPrototype(std::ostream &os, unsigned indent);
};

class Template final : public FunDef {
public:
  Template(Location loc, const char *n, const Type *t, std::vector<VarDec *> p,
           Block *b, std::vector<TempParamDec *> tp);

  const std::vector<TempParamDec *> &tempParams() const { return tempParams_; };

  void display(std::ostream &os, unsigned indent) override;
  void bindParams(const std::vector<Expression *> &a);
  void resetParams();

  Sexpression *ACL2Expr() override;

private:
  std::vector<TempParamDec *> tempParams_;
};

#endif // FUNCTIONS_H
