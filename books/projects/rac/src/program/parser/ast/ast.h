#ifndef AST_H
#define AST_H

#include "fwd.h"

#include "../utils/diagnostics.h"

#include <vector>

// A program consists of type definitions, global constant declarations, and
// function definitions.
class AST {
public:
  AST();
  AST(AST &&ast);

  DiagnosticHandler &diag() { return diag_; }

  // Add anew type/constant/function to the program. Those should only be
  // called in the parser. Return false if the registration failed (they is
  // already something with the same name).
  bool registerType(DefinedType *t);
  void registerGlobal(VarDec *d);
  void registerTemplate(Template *t);
  void registerFunDef(FunDef *t);

  // Get an type/dec/function called `name`. Return nullptr if nothing was
  // registered with this name.
  DefinedType *getType(const std::string &name);
  VarDec *getGlobal(const std::string &name);
  Template *getTemplate(const std::string &name);
  FunDef *getFunDef(const std::string &name);
  Builtin *getBuiltin(const std::string &name);

  bool isEmpty() const;

protected:
  std::vector<DefinedType *> typeDefs_;
  std::vector<VarDec *> globals_;
  std::vector<FunDef *> funDefs_;
  std::vector<Builtin *> builtins_;

  DiagnosticHandler diag_;
};

#endif // AST_H
