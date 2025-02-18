#include "../../sexpressions.h"
#include "../utils/utils.h"
#include "expressions.h"
#include "functions.h"
#include "types.h"

#include <algorithm>
#include <iomanip>
#include <sstream>

//***********************************************************************************
// class FunDef
//***********************************************************************************

FunDef::FunDef(Location loc, std::string name, Type *returnType,
               std::vector<VarDec *> p, Block *b)
    : Statement(idOf(this), loc), name_(std::move(name)),
      returnType_(returnType), params_(std::move(p)), body_(b) {}

FunDef::FunDef(NodesId id, Location loc, std::string name, Type *returnType,
               std::vector<VarDec *> p, Block *b)
    : Statement(id, loc), name_(std::move(name)), returnType_(returnType),
      params_(std::move(p)), body_(b) {}

void FunDef::displayPrototype(std::ostream &os, unsigned indent) {

  if (indent)
    os << std::setw(indent) << ' ';

  returnType_->display(os);

  os << ' ' << getname() << '(';

  bool is_first = true;
  for (auto v : params_) {
    if (!is_first)
      os << ", ";
    v->displaySimple(os);
    is_first = false;
  }

  os << ')';
}

void FunDef::display(std::ostream &os, unsigned indent) {

  os << '\n';
  displayPrototype(os, indent);
  body_->display(os, indent + 2);
  os << '\n';
}

Symbol s_funcdef("funcdef");

Sexpression *FunDef::ACL2Expr() {

  Plist *sparams = new Plist();
  for (auto v : params_) {
    sparams->add(v->sym);
  }

  return new Plist({ &s_funcdef, new Symbol(name_), sparams,
                     body_->blockify()->ACL2Expr() });
}

// class Template : public FunDef
// -----------------------------

Template::Template(Location loc, const char *n, Type *t,
                   std::vector<VarDec *> p, Block *b,
                   std::vector<TempParamDec *> tp)
    : FunDef(idOf(this), loc, n, t, p, b), tempParams_(tp) {}

void Template::display(std::ostream &os, unsigned indent) {
  os << '\n';
  if (indent)
    os << std::setw(indent) << ' ';

  os << "template<";
  bool first = true;
  for (auto p : tempParams_) {
    if (!first) {
      os << ", ";
    }
    first = false;
    p->displaySymDec(os);
  }
  os << '>';
  FunDef::display(os, indent);
}

void Template::bindParams(const std::vector<Expression *> &actuals) {

  auto it = actuals.begin();
  for (auto formal : tempParams_) {
    assert(it != actuals.end());
    formal->init = *it;
    ++it;
  }
}

void Template::resetParams() {

  for (auto formal : tempParams_) {
    formal->init = nullptr;
  }
}

Sexpression *Template::ACL2Expr() {

  Plist *sparams = new Plist();
  for (auto v : tempParams_) {
    sparams->add(v->sym);
  }

  for (auto v : params_) {
    sparams->add(v->sym);
  }

  auto res = new Plist({ &s_funcdef, new Symbol(name_), sparams,
                         body_->blockify()->ACL2Expr() });

  return res;
}
