#ifndef PARSER_H
#define PARSER_H

#include <stdio.h>
#include <assert.h>
#include <iostream>
#include <sstream>
#include <cstring>     // for strlen, strcpy, etc
#include <stdlib.h>    // for strtol, atoi
#include <iomanip>

#include <vector>
#include <optional>
#include <deque>

using namespace std;

class Program;

extern int yylineno;

extern int  yyparse();
extern FILE *yyin;
extern FILE *yyout;
extern Program prog;

#define UNREACHABLE() assert(!"Woopsie, some unreachable was reach")

extern int yylineno;
extern char yyfilenm[];


//***********************************************************************************
// Linked Lists
//***********************************************************************************

template <class T>
class List {
public:
  T *value;
  List<T> *next;
  List<T>(T *v, List<T> *n = nullptr) {value = v; next = n;}
  List<T>(T *v1, T *v2) {value = v1; next = new List<T>(v2);}
  unsigned length();
  List<T> *nthl(unsigned n);
  T* nth(unsigned n);
  T* find(const char *name);
  bool isMember(T *ptr);
  List<T> *add(T *value);
  List<T>* push(T* value);
  List<T>* pop();
  List<T>* copy();
  void displayList(ostream& os, unsigned indent=0) const;
  void displayDefs(ostream& os) const;
};

// Length of a list;

template <class T>
unsigned List<T>::length() {
  unsigned result = 0;
  List<T> *ptr = this;
  while (ptr) {
    result++;
    ptr = ptr->next;
  }
  return result;
}

// nth sublist of a list;

template <class T>
List<T>* List<T>::nthl(unsigned n) {
  List<T> *ptr = this;
  while (ptr && n) {
    ptr = ptr->next;
    n--;
  }
  return ptr;
}

// nth element of a list;

template <class T>
T* List<T>::nth(unsigned n) {return this->nthl(n)->value;}

// Add a new element to the end of a list:

template <class T>
List<T>* List<T>::add(T *value) {
  List<T> *ptr = this;
  while (ptr->next) {
    ptr = ptr->next;
  }
  ptr->next = new List<T>(value);
  return this;
}

// Add a new element to the front of a list and return a pointer to the new list:

template <class T>
List<T>* List<T>::push(T* value) {
  return new List<T>(value, this);
}

// Find an element in the list with a given name:

template <class T>
T* List<T>::find(const char *name) {
  List<T> *ptr = this;
  while (ptr) {
    if (!strcmp(ptr->value->getname(), name)) {
      return ptr->value;
    }
    ptr = ptr->next;
  }
  return nullptr;
}

// Find a given object in a list:

template <class T>
bool List<T>::isMember(T *ptr) {
  List<T> *lst = this;
  while (lst) {
    if (lst->value == ptr) {
      return true;
    }
    lst = lst->next;
  }
  return false;
}

// Remove the head of a list and return a pointer to the tail:

template <class T>
List<T>* List<T>::pop() {
  List<T>* result = this->next;
  delete this;
  return result;
}

// Create a copy of a list:

template <class T>
List<T>* List<T>::copy() {
  List<T>* result = new List<T>(value);
  List<T> *ptr = next;
  while (ptr) {
    result->add(ptr->value);
    ptr = ptr->next;
  }
  return result;
}

// Call "display" on each element of a list:

template <class T>
void List<T>::displayList(ostream& os, unsigned indent) const {
  const List<T> *ptr = this;
  while (ptr) {
    ptr->value->display(os, indent);
    ptr = ptr->next;
 }
}

// Call "displayDef" on each element of a list:

template <class T>
void List<T>::displayDefs(ostream& os) const {
  List<T> *ptr = this;
  while (ptr) {
    ptr->value->displayDef(os);
    ptr = ptr->next;
 }
}


// BigList: a list with a pointer to the last entry, designed for a fast add operation

template <class T>
class BigList {
public:
  List<T> *front;
  List<T> *back;
  BigList<T>(T *v) {
    front = new List<T>(v);
    back = front;
  }
  BigList<T> *add(T *v) {
    back->next = new List<T>(v);
    back = back->next;
    return this;
  }
};


// Stacks:

template <typename T>
class SymbolStack {
// We use a deque to store all values and we use nullptr to mark the limit
// between frames. All values are sorted from last to be pushed to first (this
// is done cheaply by deque push_front()) and thus searching should be more or
// less efficient (we are traversing the addresses from low to high).
public:
  void push(T *value) {
    assert(value && "this stack does not support nullptr ias value");
    data_.push_front(value);
  }

  void pushFrame() {
    data_.push_front(nullptr);
  }

  void popFrame() {
    // While there is some values in the vector and the last one is not null
    // (the end of the last frame), we remove the element of the last frame.
    while (data_.size() && data_.front()) {
      data_.pop_front();
    }
  }

  T *find(const char *name) {
    for (auto it = begin(data_); it != end(data_); ++it) {
      // Detect the limit of frame and ingore it.
      if (!*it) {
        continue;
      }

      if (!strcmp((*it)->getname(), name)) {
        return *it;
      }
    }
    return nullptr;
  }

private:
  std::deque<T *> data_;
};


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


//***********************************************************************************
// Types
//***********************************************************************************

class Expression;
class SymRef;

// Derived classes:
//
//   PrimType           (primitive type: uintTYpe, intType, boolType)
//   DefinedType        (introduced by typedef)
//   RegType            (Algorithmic C register type)
//   UintType           (unsigned limited integer register)
//   IntType            (signed limited integer register)
//   FPType             (fixed-point register
//   UfixedType         (unsigned fixed-point register
//   FixedType          (signed fixed-point register
//   ArrayType          (array type)
//   ArrayParamType     (array template class, which may be passed as parameter)
//   StructType         (struct type)
//   EnumType           (enumeration type)
//   MvType             (multiple value type)
class Type {
public:
  // overridden by PrimType
  virtual bool isPrimType() const { return false; }
  // overridden by RegType
  virtual bool isRegType() const { return false; }
  // overridden by FPType
  virtual bool isArrayType() const { return false; }
  // overridden by ArrayType
  virtual bool isArrayParamType() const { return false; }
  // overridden by ArrayParamType
  virtual bool isStructType() const { return false; }
  // overridden by StructType
  virtual bool isIntegerType() const { return false; }
  // overridden by EnumType
  virtual bool isFPType() const { return false; }
  // overridden by integer types
  virtual bool isEnumType() const { return false; }
  // overridden by DefinedType
  virtual Type *derefType() { return this; }
  virtual void display(ostream& os=cout) const = 0;

  virtual void displayVarType(ostream& os=cout) const {
    // How this type is displayed in a variable declaration
    display(os);
  }

  // overridden by ArrayType
  virtual void displayVarName([[maybe_unused]] const char *name, ostream& os=cout) {
    // How a variable of this type is displayed in a variable declaration
    display(os);
  } 

  // overridden by ArrayType, StructType, and EnumType
  virtual void makeDef([[maybe_unused]] const char *name, ostream& os=cout) {
    // How this type is displayed in a type definition.
    os << "\ntypedef ";
    display(os);
    os << " " << name << ";";
  }

  // overridden by RegType 
  virtual Sexpression *ACL2Assign(Expression *rval);
//    // Convert rval to an S-expression to be assigned to an object of this type.
//    return rval->ACL2Expr();
//  }

  // overridden by UintType
  virtual unsigned ACL2ValWidth() { 
  // Boundary on the width of the value of an object of this type.
  // 0 indicates unknown or unbounded width.
  // Used to avoid unnecessary call to bits.
  return 0;
  }

  // overridden by RegType
  virtual Sexpression *ACL2Eval(Sexpression *s) {
    // For a RegType, the numerical value represented by a given bit vector s.
    // For any other type, just return s.
    return s;
  }
};

class PrimType : public Symbol, public Type {
public:
  PrimType(const char *s, const char *m=nullptr)
    : Symbol(s)
    , RACname_(m ? std::optional(std::string(m)) : nullopt) {
  }

  bool isPrimType() const override { return true; }
  bool isIntegerType() const override { return true; }

  void display(ostream& os) const {
    if (RACname_) {
      os << *RACname_;
    }
    else {
      Symbol::display(os);
    }
  }

private:
  const std::optional<std::string> RACname_;
};

extern PrimType boolType;
extern PrimType intType;
extern PrimType uintType;
extern PrimType int64Type;
extern PrimType uint64Type;

class DefinedType : public Symbol, public Type {
public:
  DefinedType(const char *s, Type *t)
    : Symbol(s)
    , def_(t) {
  }

  void display(ostream& os) const { Symbol::display(os); }

  void displayDef(ostream& os=cout) const {
    if (!(def_->isRegType())) {
      def_->makeDef(getname(), os);
    }
  }

  Type *getdef() { return def_; }
  Type *& getdef_mutref() { return def_; }
  Type *derefType() { return def_->derefType(); }

private:
  Type *def_;
};

class RegType : public Type {
public:
  RegType(Expression *w)
    : width_(w) {
  }

  Expression *width() const { return width_; }

  bool isRegType() const override { return true; }
  Sexpression *ACL2Assign(Expression *rval);

private:
  Expression *width_;
};

class UintType : public RegType {
public:
  UintType(Expression *w);
  bool isIntegerType() const override { return true; }
  void display(ostream& os=cout) const;
  unsigned ACL2ValWidth();
};

class IntType : public RegType {
public:
  bool isSigned();
  IntType(Expression *w);
  bool isIntegerType() const override { return true; }
  void display(ostream& os=cout) const;
  Sexpression *ACL2Eval(Sexpression *s);
};

class FPType :public RegType {
public:
  Expression *iwidth;
  FPType(Expression *w, Expression *iw);
  bool isFPType() const override { return true; }
  Sexpression *ACL2Assign(Expression *rval);
};

class UfixedType :public FPType {
public:
  UfixedType(Expression *w, Expression *iw);
  void display(ostream& os=cout) const;
  Sexpression *ACL2Eval(Sexpression *s);
};

class FixedType :public FPType {
public:
  bool isSigned();
  FixedType(Expression *w, Expression *iw);
  void display(ostream& os=cout) const;
  Sexpression *ACL2Eval(Sexpression *s);
};

class ArrayType : public Type {
public:
  Type *baseType;
  Expression *dim;

  ArrayType(Expression *d, Type *t)
    : baseType(t)
    , dim(d) {
  }

  Type *getBaseType();
  bool isArrayType() const override { return true; }
  void display(ostream& os) const;
  void displayVarType(ostream& os=cout) const;
  void displayVarName(const char *name, ostream& os=cout) const;
  void makeDef(const char *name, ostream& os);
};

class ArrayParamType : public ArrayType {
public:
  ArrayParamType(Expression *d, Type *t);
  bool isArrayParamType() const override { return true; }
  void display(ostream& os) const;
  void displayVarType(ostream& os=cout) const;
  void displayVarName(const char *name, ostream& os=cout) const;
  void makeDef(const char *name, ostream& os);
};

class StructField {
public:
  Symbol *sym;
  Type *type;
  StructField(Type *t, char *n);
  const char *getname() const { return sym->getname(); }
  void display(ostream& os, unsigned indent=0) const;
};

class StructType : public Type {
public:
  List<StructField> *fields;
  StructType(List<StructField> *f);
  bool isStructType() const override { return true; }
  void displayFields(ostream& os) const;
  void display(ostream& os) const;
  void makeDef(const char *name, ostream& os=cout);
};

class Expression;

class SymDec {
public:
  Symbol* sym;
  Type *type;
  Expression *init;
  SymDec(const char *n, Type *t, Expression *i = nullptr);
  const char *getname() const { return sym->getname(); }
  void displaySymDec(ostream& os) const;
  virtual bool isGlobal();
  virtual bool isROM();
  virtual bool isConst();
  virtual int evalConst();
  virtual Sexpression *ACL2SymExpr();
};

class EnumConstDec : public SymDec {
public:
  EnumConstDec(const char *n, Expression *v=nullptr);
  void display(ostream& os) const;
  bool isConst();
  Sexpression *ACL2Expr();
  Sexpression *ACL2SymExpr();
};

class EnumType : public Type {
public:
  List<EnumConstDec> *vals;
  EnumType(List<EnumConstDec> *v);
  bool isEnumType() const override { return true; }
  bool isIntegerType() const override { return true; }
  void displayConsts(ostream& os) const;
  void display(ostream& os) const;
  void makeDef(const char *name, ostream& os=cout);
  Sexpression *ACL2Expr();
  Sexpression *getEnumVal(Symbol *s);
};

class MvType : public Type {
public:
  std::vector<Type *> type;
  MvType(std::initializer_list<Type* >&& t)
    : type(t) {
  }
  void display(ostream& os) const;
};

//***********************************************************************************
// Expressions
//***********************************************************************************

class Statement;
class SymRef;
class SymDec;
class Constant;

class Expression {
public:
  bool needsParens;
  Expression();
  virtual bool isConst();
  virtual int evalConst();
  virtual bool isArray();
  virtual bool isArrayParam();
  virtual bool isStruct();
  bool isNumber();
  virtual bool isSubrange();
  virtual bool isSymRef();
  virtual bool isInteger();
  virtual bool isInitializer();
  bool isFP();
  virtual Type* exprType();
  void display(ostream& os) const;
  virtual void displayNoParens(ostream& os) const = 0;
  virtual Expression *subst(SymRef *var, Expression *val);
  virtual Sexpression *ACL2Expr(bool isBV = false);
  virtual Sexpression *ACL2ArrayExpr();
  virtual Sexpression *ACL2Assign(Sexpression *rval);
  virtual unsigned ACL2ValWidth();
  virtual bool isEqual(Expression *e);
  virtual bool isEqualPrefix(const char *o, Expression *e);
  virtual bool isEqualBinary(const char *o, Expression *e1, Expression *e2);
  virtual bool isPlusConst(Expression *e);
  virtual int getPlusConst();
  virtual bool isEqualSymRef(SymDec *s);
  virtual bool isEqualConst(Constant *c);
};

class Constant : public Expression, public Symbol {
public:
  Constant(const char *n);
  Constant(int n);
  bool isConst();
  bool isInteger() override { return true; }
  void displayNoParens(ostream& os) const;
  Sexpression *ACL2Expr(bool isBV = false);
  bool isEqual(Expression *e);
  bool isEqualConst(Constant *c);
};

class Integer : public Constant{
public:
  Integer(const char *n);
  Integer(int n);
  int evalConst();
  Sexpression *ACL2Expr(bool isBV);
};

extern Integer i_0;
extern Integer i_1;
extern Integer i_2;

class Boolean : public Constant {
public:
  Boolean(const char *n);
  int evalConst();
  Sexpression *ACL2Expr(bool isBV = false);
};

extern Boolean b_true;
extern Boolean b_false;

class SymRef : public Expression {
public:
  SymDec *symDec;
  SymRef(SymDec *s);
  bool isSymRef();
  Type* exprType();
  virtual bool isConst();
  virtual int evalConst();
  bool isArray();
  bool isArrayParam();
  bool isStruct();
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
  bool isEqual(Expression *e);
  bool isEqualSymRef(SymDec *s);
};

class FunDef;

class FunCall : public Expression {
public:
  FunDef *func;
  List<Expression> *args;
  FunCall(FunDef *f, List<Expression> *a);
  bool isArray();
  bool isArrayParam();
  bool isStruct();
  bool isInteger() override;
  Type* exprType();
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class Template;

class TempCall : public FunCall {
public:
  Symbol *instanceSym;
  List<Expression> *params;
  TempCall(Template *f, List<Expression> *a, List<Expression> *p);
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class Initializer : public Expression {
public:
  List<Constant> *vals;
  Initializer(List<Constant> *v);
  bool isInitializer();
  void displayNoParens(ostream& os) const;
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2ArrayExpr();
  Sexpression *ACL2StructExpr(List<StructField> *fields);
};

class ArrayRef : public Expression {
public:
  Expression *array;
  Expression *index;
  ArrayRef(Expression *a, Expression *i);
  bool isArray();
  bool isArrayParam();
  bool isInteger() override;
  Type* exprType();
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
};

class ArrayParamRef : public ArrayRef {
public:
  ArrayParamRef(Expression *a, Expression *i);
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
};

class StructRef : public Expression {
public:
  Expression *base;
  char *field;
  StructRef(Expression *s, char *f);
  bool isArray();
  bool isArrayParam();
  bool isInteger() override;
  Type* exprType();
  void displayNoParens(ostream& os) const;
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
};

class BitRef : public Expression {
public:
  Expression *base;
  Expression *index;
  BitRef(Expression *b, Expression *i);
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
  unsigned ACL2ValWidth();
};

class Subrange : public Expression {
public:
  Expression *base;
  Expression *high;
  Expression *low;
  unsigned width;
  Subrange(Expression *b, Expression *h, Expression *l);
  Subrange(Expression *b, Expression *h, Expression *l, unsigned w);
  bool isSubrange();
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
  unsigned ACL2ValWidth();
};

class PrefixExpr : public Expression {
public:
  Expression *expr;
  const char *op;
  PrefixExpr(Expression *e, const char *o);
  bool isConst();
  int evalConst();
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Type *exprType();
  Sexpression *ACL2Expr(bool isBV = false);
  virtual bool isEqual(Expression *e);
  virtual bool isEqualPrefix(const char *o, Expression *e);
};

class CastExpr : public Expression {
public:
  Expression *expr;
  Type *type;
  CastExpr(Expression *e, Type *t);
  Type* exprType();
  bool isConst();
  int evalConst();
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class BinaryExpr : public Expression {
protected:
public:
  Expression *expr1;
  Expression *expr2;
  const char *op;
  BinaryExpr(Expression *e1, Expression *e2, const char *o);
  bool isConst();
  int evalConst();
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Type *exprType();
  Sexpression *ACL2Expr(bool isBV = false);
  virtual bool isEqual(Expression *e);
  virtual bool isEqualBinary(const char *o, Expression *e1, Expression *e2);
  virtual bool isPlusConst(Expression *e);
  virtual int getPlusConst();
};

class CondExpr : public Expression {
public:
  Expression *expr1;
  Expression *expr2;
  Expression *test;
  CondExpr(Expression *e1, Expression *e2, Expression *t);
  bool isInteger() override;
  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class MultipleValue : public Expression {
public:
  MvType *type;
  std::vector<Expression *> expr;

  MultipleValue(MvType *t, std::vector<Expression *>&& e)
    : type(t)
    , expr(e) {
  }
  MultipleValue(MvType *t, List<Expression> *e);

  void displayNoParens(ostream& os) const;
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

//***********************************************************************************
// Statements
//***********************************************************************************

class Block;

class Statement {
public:
  Statement();
  virtual void display(ostream& os, unsigned indent=0) = 0;
  virtual void displayAsRightBranch(ostream& os, unsigned indent=0);
  virtual void displayWithinBlock(ostream& os, unsigned indent=0);
  virtual Block *blockify();
  virtual Block *blockify(Statement *s);
  virtual Statement* subst(SymRef *var, Expression *expr);
  virtual Sexpression *ACL2Expr();
  virtual void noteReturnType(Type *t);
  virtual void markAssertions(FunDef *f);
};

class SimpleStatement : public Statement {
public:
  SimpleStatement();
  void display(ostream& os, unsigned indent=0);
  virtual void displaySimple(ostream& os) = 0;
};

class VarDec : public SimpleStatement, public SymDec {
public:
  VarDec(const char *n, Type *t, Expression *i = nullptr);
  void displaySimple(ostream& os);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  Sexpression *ACL2SymExpr();
};

class ConstDec : public VarDec {
public:
  ConstDec(const char *n, Type *t, Expression *i);
  void displaySimple(ostream& os);
  Statement *subst(SymRef *var, Expression *val);
  bool isConst();
  bool isGlobal();
  bool isROM();
  Sexpression *ACL2SymExpr();
};

class MulVarDec : public SimpleStatement {
public:
  List<VarDec> *decs;
  MulVarDec(VarDec *dec1, VarDec *dec2);
  MulVarDec(List<VarDec> *decs);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void displaySimple(ostream& os);
};

class MulConstDec : public SimpleStatement {
public:
  List<ConstDec> *decs;
  MulConstDec(ConstDec *dec1, ConstDec *dec2);
  MulConstDec(List<ConstDec> *decs);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void displaySimple(ostream& os);
};

class TempParamDec : public SymDec {
public:
  TempParamDec(const char *n, Type *t);
  bool isConst();
  Sexpression *ACL2SymExpr();
};

class BreakStmt : public SimpleStatement {
public:
  BreakStmt();
  void displaySimple(ostream& os);
  Sexpression *ACL2Expr();
};

class ReturnStmt : public SimpleStatement {
public:
  Expression *value;
  Type *returnType;
  ReturnStmt(Expression *v);
  void displaySimple(ostream& os);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void noteReturnType(Type *t);
};

class NullStmt : public SimpleStatement {
public:
  NullStmt();
  void displaySimple(ostream& os);
  Sexpression *ACL2Expr();
};

class Assertion : public SimpleStatement {
public:
  Expression *expr;
  FunDef *funDef;
  Assertion(Expression *e);
  void displaySimple(ostream& os);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void markAssertions(FunDef *f);
};

class Assignment : public SimpleStatement {
public:
  Expression *lval;
  const char* op;
  Expression *rval;
  Assignment(Expression *l, const char *o, Expression *r=nullptr);
  void displaySimple(ostream& os);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
};

class AssignBit : public SimpleStatement {
public:
  Expression *base;
  Expression *index;
  Expression *val;
  AssignBit(Expression *b, Expression *i, Expression *v);
  void displaySimple(ostream& os);
};

class AssignRange : public SimpleStatement {
public:
  Expression *base;
  Expression *high;
  Expression *low;
  Expression *width;
  Expression *val;
  AssignRange(Expression *b, Expression *h, Expression *l, Expression *w, Expression *v);
  void displaySimple(ostream& os);
};

class AssignFull : public SimpleStatement {
public:
  Expression *base;
  unsigned width;
  Expression *val;
  AssignFull(Expression *b, unsigned w, Expression *v);
  void displaySimple(ostream& os);
};

class MultipleAssignment : public SimpleStatement {
public:
  Expression *lval[8];
  FunCall *rval;
  MultipleAssignment(FunCall *r, List<Expression> *e);
  void displaySimple(ostream& os);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
};

class Block : public Statement {
public:
  List<Statement> *stmtList;
  Block(List<Statement> *s);
  Block(Statement* s);
  Block(Statement* s1, Statement* s2);
  Block(Statement* s1, Statement* s2, Statement* s3);
  Block *blockify();
  Block *blockify(Statement *s);
  void display(ostream& os, unsigned indent=0);
  void displayWithinBlock(ostream& os, unsigned indent=0);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void noteReturnType(Type *t);
  void markAssertions(FunDef *f);
};

class IfStmt : public Statement {
public:
  Expression *test;
  Statement *left;
  Statement *right;
  IfStmt(Expression *t, Statement *l, Statement *r);
  void display(ostream& os, unsigned indent=0);
  void displayAsRightBranch(ostream& os, unsigned indent=0);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void markAssertions(FunDef *f);
  void noteReturnType(Type *t);
};

class ForStmt : public Statement {
public:
  SimpleStatement *init;
  Expression *test;
  Assignment *update;
  Statement *body;
  ForStmt(SimpleStatement *v, Expression *t, Assignment *u, Statement *b);
  void display(ostream& os, unsigned indent=0);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void markAssertions(FunDef *f);
};

class Case {
public:
  Expression *label;
  List<Statement> *action;
  Case(Expression *l, List<Statement> *a);
  void display(ostream& os, unsigned indent=0);
  Case* subst(SymRef *var, Expression *val);
  void markAssertions(FunDef *f);
};

class SwitchStmt : public Statement {
public:
  Expression *test;
  List<Case> *cases;
  SwitchStmt(Expression *t, List<Case> *c);
  void display(ostream& os, unsigned indent=0);
  Statement* subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void markAssertions(FunDef *f);
};

//***********************************************************************************
// Functions
//***********************************************************************************

class FunDef {
public:
  Symbol *sym;
  Type *returnType;
  List<VarDec> *params;
  Block *body;
  FunDef(const char *n, Type *t, List<VarDec> *p, Block *b);
  unsigned arity();
  const char *getname() const { return sym->getname(); }
  void displayDec(ostream& os, unsigned indent=0);
  virtual void display(ostream& os, const char *prefix = "", unsigned indent=0);
  virtual void displayACL2Expr(ostream& os);
};

class Builtin : public FunDef {
public:
  Builtin(const char *n, Type *t, Type *a0=nullptr, Type *a1=nullptr, Type *a2=nullptr);
};

class Template : public FunDef{
public:
  List<TempParamDec> *tempParams;
  List<TempCall> *calls;
  Template(const char *n, Type *t, List<VarDec> *p, Block *b, List<TempParamDec> *tp);
  void display(ostream& os, const char *prefix = "", unsigned indent=0);
  void addCall(TempCall *c);
  void bindParams(List<Expression> *a);
  void displayACL2Expr(ostream& os);
};

//***********************************************************************************
// Programs
//***********************************************************************************

enum class DispMode {rac, acl2};

class Program {
public:
  List<DefinedType> *typeDefs;
  List<ConstDec> *constDecs;
  List<Template> *templates;
  List<FunDef> *funDefs;
  Program();
  void displayTypeDefs(ostream& os, DispMode mode);
  void displayConstDecs(ostream& os, DispMode mode);
  void displayTemplates(ostream& os, DispMode mode, const char *prefix="");
  void displayFunDefs(ostream& os, DispMode mode, const char *prefix="");
  void displayFunDecs(ostream& os);
  void display(ostream& os, DispMode mode=DispMode::rac);
  bool isEmpty() const;
};

extern Program prog;

#endif
