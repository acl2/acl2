#ifndef FUNCTIONS_H
#define FUNCTIONS_H

#include "statements.h"
#include "utils.h"

#include <iomanip>

using namespace std;

//***********************************************************************************
// Functions
//***********************************************************************************

// Same why not is hierarchy
class FunDef
{
protected:
  Symbol *sym;

public:
  Type *returnType;
  List<VarDec> *params;
  Block *body;

  FunDef (const char *n, Type *t, List<VarDec> *p, Block *b);

  const char *
  getname () const
  {
    return sym->getname ();
  }

  void displayDec (ostream &os, const char *prefix = "", unsigned indent = 0);
  virtual void display (ostream &os, const char *prefix = "",
                        unsigned indent = 0);
  virtual void displayACL2Expr (ostream &os);

private:
  void displayPrototype (ostream &os, const char *prefix, unsigned indent);
};

class Builtin : public FunDef
{
public:
  Builtin (const char *n, Type *t, List<VarDec> *p)
    : FunDef(n, t, p, nullptr)
  {
  }
};

class Template : public FunDef
{
public:
  List<TempParamDec> *tempParams;
  List<TempCall> *calls;
  Template (const char *n, Type *t, List<VarDec> *p, Block *b,
            List<TempParamDec> *tp);
  void display (ostream &os, const char *prefix = "",
                unsigned indent = 0) override;
  void addCall (TempCall *c);
  void bindParams (List<Expression> *a);
  void displayACL2Expr (ostream &os) override;
};

#endif // FUNCTIONS_H
