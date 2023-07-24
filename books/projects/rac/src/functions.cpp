#include "functions.h"

#include <sstream>

//***********************************************************************************
// class FunDef
//***********************************************************************************

// Data members: Symbol *sym; Type *returnType; List<VarDec> *params; Block
// *body;

FunDef::FunDef(const char *n, Type *t, List<VarDec> *p, Block *b)
    : sym(new Symbol(n)), returnType(t), params(p), body(b) {}

void FunDef::displayPrototype(ostream &os, const char *prefix,
                              unsigned indent) {
  os << "\n";

  if (indent)
    os << setw(indent) << " ";

  returnType->display(os);

  os << " " << prefix << getname() << "(";

  bool is_first = true;
  for_each(params, [&](VarDec *v) {
    if (!is_first)
      os << ", ";
    v->displaySimple(os);
    is_first = false;
  });

  os << ")";
}

void FunDef::displayDec(ostream &os, const char *prefix, unsigned indent) {
  displayPrototype(os, prefix, indent);
  os << ';';
}

void FunDef::display(ostream &os, const char *prefix, unsigned indent) {

  displayPrototype(os, prefix, indent);
  body->display(os, indent + 2);
  os << "\n";
}

Symbol s_funcdef("funcdef");

void FunDef::displayACL2Expr(ostream &os) {

  Plist *sparams = new Plist();
  for_each(params, [&sparams](VarDec *v) { sparams->add(v->sym); });

  body->noteReturnType(returnType);
  body->markAssertions(this);

  Plist({ &s_funcdef, sym, sparams, body->blockify()->ACL2Expr() })
      .display(os);

  delete sparams;
}

// class Template : public FunDef
// -----------------------------

// Data members: List<TempParamDec> *tempParams; List<TempCall> *calls;

Template::Template(const char *n, Type *t, List<VarDec> *p, Block *b,
                   List<TempParamDec> *tp)
    : FunDef(n, t, p, b), tempParams(tp) {}

void Template::display(ostream &os, const char *prefix, unsigned indent) {
  os << "\n";
  if (indent)
    os << setw(indent) << " ";

  os << "template<";
  List<TempParamDec> *ptr = tempParams;
  while (ptr) {
    ptr->value->displaySymDec(os);
    ptr = ptr->next;
    if (ptr) {
      os << ", ";
    }
  }
  os << ">";
  FunDef::display(os, prefix, indent);
}

void Template::addCall(TempCall *c) {
  if (calls) {
    calls->add(c);
  } else {
    calls = new List<TempCall>(c);
  }
}

// This is called by both Template::displayACL2Expr and TempCall::ACL2Expr:

void Template::bindParams(List<Expression> *actuals) {
  List<TempParamDec> *formals = tempParams;
  while (formals) {
    assert(actuals);
    formals->value->init = actuals->value, formals = formals->next;
    actuals = actuals->next;
  }
}

void Template::displayACL2Expr(ostream &os) {
  List<TempCall> *c = calls;
  unsigned numCalls = 0;
  Symbol *saveSym = sym;
  while (c) {
    ostringstream ostr;
    ostr << saveSym->getname() << "-" << numCalls++;
    string st = ostr.str();
    const char *name = st.c_str();
    sym = new Symbol(name);
    c->value->instanceSym = sym;
    bindParams(c->value->params);
    FunDef::displayACL2Expr(os);
    c = c->next;
  }
  sym = saveSym;
}
