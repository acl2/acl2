#include <algorithm>

#include "statements.h"
#include "types.h"

//***********************************************************************************
// Programs
//***********************************************************************************

enum class DispMode {
  rac,
  acl2,
  none,
};

// A program consists of type definitions, global constant declarations, and
// function definitions.
class Program {
  std::vector<DefinedType *> typeDefs;

public:
  List<ConstDec> *constDecs;
  List<Template> *templates;
  List<FunDef> *funDefs;

  Program();
  void displayTypeDefs(std::ostream &os, DispMode mode) const;

  // TODO constify ACL2Exp, then this can become const
  void displayConstDecs(std::ostream &os, DispMode mode);

  // Why this one is not defined
  //  void displayTemplates(std::ostream& os, DispMode mode, const char
  //  *prefix="");

  void displayFunDefs(std::ostream &os, DispMode mode);
  void displayFunDecs(std::ostream &os) const;
  void display(std::ostream &os, DispMode mode = DispMode::rac);
  bool isEmpty() const;

  std::optional<DefinedType *> findDefinedType(const std::string &name) {

    auto it = std::find_if(
        typeDefs.begin(), typeDefs.end(),
        [&name](DefinedType *dt) { return dt->name() == name; });
    return it == typeDefs.end() ? std::nullopt : std::optional(*it);
  }

  void registerType(DefinedType *dt) { typeDefs.push_back(dt); }
};

extern Program prog;
