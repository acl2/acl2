#ifndef PARSER_H
#define PARSER_H

#include <stdio.h>
#include <assert.h>
#include <iostream>
#include <cstring>     // for strlen, strcpy, etc

#include <vector>
#include <optional>
#include <deque>

#include "utils.h"

using namespace std;

class Program;

extern int yylineno;

extern int  yyparse();
extern FILE *yyin;
extern FILE *yyout;
extern Program prog;

extern int yylineno;
extern char yyfilenm[];

//***********************************************************************************
// S-Expressions
//***********************************************************************************

// An Sexpression is a Symbol, a Cons, or a Plist (proper list of S-expressions).
// Note that Constant is a derived class of Symbol.
class Sexpression {
public:
  virtual void display(ostream& os) const = 0;
};

class Plist : public Sexpression {
public:
  // TODO list -> private
  List<Sexpression> *list;

  Plist()
    : list(nullptr) {
  };

  Plist(std::initializer_list<Sexpression *> sexprs) {

    auto it = crbegin(sexprs);
    if (it == crend(sexprs)) {
      list = nullptr;
      return;
    }

    list = new List<Sexpression>(*it);
    for (++it; it != crend(sexprs); ++it) {
      list = list->push(*it);
    }
  }

  static Plist *FromList(List<Sexpression> *l=nullptr) {
    auto pl = new Plist();
    pl->list = l;
    return pl;
  }

  Plist *add(Sexpression *s) {
    if (list) {
      list->add(s);
    }
    else {
      list = new List<Sexpression>(s);
    }
    return this;
  }

  Plist *push(Sexpression *s) {
    if (list) {
      list = list->push(s);
    }
    else {
      list = new List<Sexpression>(s);
    }
    return this;
  }

  void display(ostream& os) const;
};

class Cons : public Sexpression {
 public:
  Cons(Sexpression *a, Sexpression *d)
    : car_(a)
    , cdr_(d) {
  }

  void display(ostream& os) const {
    os << "(";
    car_->display(os);
    os << " . ";
    cdr_->display(os);
    os << ")";
  }

private:
  Sexpression *car_;
  Sexpression *cdr_;
};

class Symbol : public Sexpression {
  std::string name_;
public:
  Symbol(std::string&& s)
    : name_(s) {
  }

  Symbol(const char *s)
    : name_(s) {
  }

  Symbol(int n)
    : name_(std::to_string(n)) {
  }

  const char *getname() const { return name_.c_str(); }
  void display(ostream& os) const { os << name_;}
};

#include "types.h"
#include "expressions.h"
#include "statements.h"
#include "functions.h"



//***********************************************************************************
// Programs
//***********************************************************************************

enum class DispMode {rac, acl2};

// A program consists of type definitions, global constant declarations, and
// function definitions.
class Program {
public:
  List<DefinedType> *typeDefs;
  List<ConstDec> *constDecs;
  List<Template> *templates;
  List<FunDef> *funDefs;

  Program()
    : typeDefs(List<DefinedType>::empty())
    , constDecs(List<ConstDec>::empty())
    , templates(List<Template>::empty())
    , funDefs(List<FunDef>::empty())
  {}

  void displayTypeDefs(ostream& os, DispMode mode) const {
    // Note that type definitions are used in generating S-expressions for
    // constant declarations and function definitions, but are not represented
    // explicitly in the ACL2 translation.
    if (mode == DispMode::rac) {
      for_each(typeDefs, [&os](auto v) { v->displayDef(os); });
    }
  }

  // TODO constify ACL2Exp, then this can become const
  void displayConstDecs(ostream& os, DispMode mode) {
    if (mode == DispMode::rac) {
      for_each(constDecs, [&os](auto v) { v->display(os); });
    } else {
      for_each(constDecs, [&os](auto v) { v->ACL2Expr()->display(os); });
    }
  }

  // Why this one is not defined
//  void displayTemplates(ostream& os, DispMode mode, const char *prefix="");

  void displayFunDefs(ostream& os, DispMode mode) {
    if (mode == DispMode::rac) {
      for_each(funDefs, [&os](auto v) { v->display(os); });
    } else {
      for_each(funDefs, [&os](auto v) { v->displayACL2Expr(os); });
    }
  }

  void displayFunDecs(ostream& os) const {
    for_each(funDefs, [&os](auto v) { v->displayDec(os); });
  }

  void display(ostream& os, DispMode mode=DispMode::rac) {
    displayTypeDefs(os, mode);
    os << "\n";
    displayConstDecs(os, mode);
    os << "\n";
    displayFunDefs(os, mode);
    os << "\n";
  }

  bool isEmpty() const {
    return !funDefs->length();
  }
};

extern Program prog;

#endif
