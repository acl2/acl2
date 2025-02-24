#include "ast.h"

#include "functions.h"
#include "statements.h"
#include "types.h"

AST::AST() {
  typeDefs_.reserve(256);
  globals_.reserve(256);
  //  templates_.reserve(256);
  funDefs_.reserve(256);

  builtins_.push_back(
      new Builtin(Location::dummy(), "abs", &intType,
                  {new VarDec(Location::dummy(), "", &intType)}));
}

AST::AST(AST &&other)
    : typeDefs_(std::move(other.typeDefs_)),
      globals_(std::move(other.globals_)),
      //      templates_(std::move(other.templates_)),
      funDefs_(std::move(other.funDefs_)), diag_(std::move(other.diag_)) {}

bool AST::registerType(const DefinedType *t) {
  if (getType(t->getname()))
    return false;
  typeDefs_.push_back(t);
  return true;
}

const DefinedType *AST::getType(const std::string &name) {
  auto it =
      std::find_if(typeDefs_.begin(), typeDefs_.end(),
                   [&](const DefinedType *t) { return name == t->getname(); });
  return it == typeDefs_.end() ? nullptr : *it;
}

void AST::registerGlobal(VarDec *d) { globals_.push_back(d); }

VarDec *AST::getGlobal(const std::string &name) {
  auto it = std::find_if(globals_.begin(), globals_.end(),
                         [&](VarDec *d) { return name == d->getname(); });
  return it == globals_.end() ? nullptr : *it;
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
