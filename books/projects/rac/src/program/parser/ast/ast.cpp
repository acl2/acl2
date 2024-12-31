#include "ast.h"

#include "expressions.h"
#include "functions.h"
#include "statements.h"
#include "types.h"

AST::AST() {
  typeDefs_.reserve(256);
  constDecs_.reserve(256);
  //  templates_.reserve(256);
  funDefs_.reserve(256);

  builtins_.push_back(
      new Builtin(Location::dummy(), "abs", &intType,
                  { new VarDec(Location::dummy(), "", &intType) }));
}

AST::AST(AST &&other)
    : typeDefs_(std::move(other.typeDefs_)),
      constDecs_(std::move(other.constDecs_)),
      //      templates_(std::move(other.templates_)),
      funDefs_(std::move(other.funDefs_)), diag_(std::move(other.diag_)) {}

bool AST::registerType(DefinedType *t) {
  if (getType(t->getname()))
    return false;
  typeDefs_.push_back(t);
  return true;
}

DefinedType *AST::getType(const std::string &name) {
  auto it = std::find_if(typeDefs_.begin(), typeDefs_.end(),
                         [&](DefinedType *t) { return name == t->getname(); });
  return it == typeDefs_.end() ? nullptr : *it;
}

void AST::registerConstDec(ConstDec *d) { constDecs_.push_back(d); }

ConstDec *AST::getConstDec(const std::string &name) {
  auto it = std::find_if(constDecs_.begin(), constDecs_.end(),
                         [&](ConstDec *d) { return name == d->getname(); });
  return it == constDecs_.end() ? nullptr : *it;
}

Template *AST::getTemplate(const std::string &name) {
  return dynamic_cast<Template *>(getFunDef(name));
}

void AST::registerFunDef(FunDef *f) { funDefs_.push_back(f); }

FunDef *AST::getFunDef(const std::string &name) {
  auto it = std::find_if(funDefs_.begin(), funDefs_.end(),
                         [&](FunDef *t) { return name == t->getname(); });
  return it == funDefs_.end() ? nullptr : *it;
}

Builtin *AST::getBuiltin(const std::string &name) {
  auto it = std::find_if(builtins_.begin(), builtins_.end(),
                         [&](Builtin *t) { return name == t->getname(); });
  return it == builtins_.end() ? nullptr : *it;
}

bool AST::isEmpty() const { return funDefs_.size() == 0; }
