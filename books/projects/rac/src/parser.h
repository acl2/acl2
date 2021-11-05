#ifndef PARSER_H
#define PARSER_H
#include <stdio.h>
#include <assert.h>
#include <iostream>
#include <sstream>
#include <cstring>     // for strlen, strcpy, etc
#include <sys/types.h> // for uint
#include <stdlib.h>    // for strtol, atoi
#include <iomanip>
using namespace std;
//#include "linkedlist.h"

extern int yylineno;
extern void yyerror(const char *);

extern char *newstr(const char *str);

//***********************************************************************************
// Linked Lists
//***********************************************************************************

template <class T>
class List {
public:
  T *value;
  List<T> *next;
  List<T>(T *v, List<T> *n = NULL) {value = v; next = n;}
  List<T>(T *v1, T *v2) {value = v1; next = new List<T>(v2);}
  uint length();
  List<T> *nthl(uint n);
  T* nth(uint n);
  T* find(char *name);
  bool isMember(T *ptr);
  List<T> *add(T *value);
  List<T>* push(T* value);
  List<T>* pop();
  List<T>* copy();
  void displayList(ostream& os, uint indent=0);
  void displayDefs(ostream& os);
};

// Length of a list;

template <class T>
uint List<T>::length() {
  uint result = 0;
  List<T> *ptr = this;
  while (ptr) {
    result++;
    ptr = ptr->next;
  }
  return result;
}

// nth sublist of a list;

template <class T>
List<T>* List<T>::nthl(uint n) {
  List<T> *ptr = this;
  while (ptr && n) {
    ptr = ptr->next;
    n--;
  }
  return ptr;
}

// nth element of a list;

template <class T>
T* List<T>::nth(uint n) {return this->nthl(n)->value;}

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
T* List<T>::find(char *name) {
  List<T> *ptr = this;
  while (ptr) {
    if (!strcmp(ptr->value->getname(), name)) {
      return ptr->value;
    }
    ptr = ptr->next;
  }
  return NULL;
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
void List<T>::displayList(ostream& os, uint indent) {
  List<T> *ptr = this;
  while (ptr) {
    ptr->value->display(os, indent);
    ptr = ptr->next;
 }
}

// Call "displayDef" on each element of a list:

template <class T>
void List<T>::displayDefs(ostream& os) {
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

template <class T>
class Stack {
private:
  List<T> *head;
  Stack<T> *next;
public:
  Stack<T>() {head = NULL; next = NULL;}
  Stack<T>(Stack<T> *n) {next = n->next; head = n->head; n->next = this;}
  void push(T *value);
  void pushFrame();
  void popFrame();
  T* find(char *name);
  void displayList(ostream& os) {head->displayList(os);}
};

// Push an element onto the stack:

template <class T>
void Stack<T>::push(T *value) {
  head = head->push(value);
}

// Push a stack frame:

template <class T>
void Stack<T>::pushFrame() {
  Stack<T> *ptr = new Stack<T>;
  ptr->head = head;
  ptr->next = next;
  next = ptr;
}

// Pop a stack frame:

template <class T>
void Stack<T>::popFrame() {
  while (head != next->head) {
    head = head->pop();
  }
  Stack<T> *temp = next->next;
  delete next;
  next = temp;
}

// Find an element in the stack:

template <class T>
T* Stack<T>::find(char *name) {
  if (head) {
    return head->find(name);
  }
  else {
    return NULL;
  }
}

//***********************************************************************************
// S-Expressions
//***********************************************************************************

class Sexpression {
public:
  virtual void display(ostream& os) = 0;
};

class Plist : public Sexpression {
public:
  List<Sexpression> *list;
  Plist(Sexpression *s);
  Plist(Sexpression *s1, Sexpression* s2);
  Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3);
  Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4);
  Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5);
  Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5, Sexpression* s6);
  Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5, Sexpression* s6, Sexpression* s7);
  Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5, Sexpression* s6, Sexpression* s7, Sexpression* s8);
  Plist(List<Sexpression> *l=NULL);
  Plist *push(Sexpression *s);
  Plist *add(Sexpression *s);
  void display(ostream& os);
};

class Cons : public Sexpression {
 public:
  Sexpression *car;
  Sexpression *cdr;
  Cons(Sexpression *a, Sexpression *d);
  void display(ostream& os);
};

class Symbol : public Sexpression {
public:
  char *name;
  Symbol(const char *s);
  Symbol(int n);
  ~Symbol();
  char *getname();
  void display(ostream& os);
};


//***********************************************************************************
// Types
//***********************************************************************************

class Expression;
class SymRef;

class Type {
public:
  virtual bool isPrimType();
  virtual bool isRegType();
  virtual bool isArrayType();
  virtual bool isArrayParamType();
  virtual bool isStructType();
  bool isNumericalType();
  virtual bool isIntegerType();
  virtual bool isFPType();
  virtual bool isEnumType();
  virtual Type *derefType();
  virtual void display(ostream& os=cout);
  virtual void displayVarType(ostream& os=cout);
  virtual void displayVarName(const char *name, ostream& os=cout);
  virtual void makeDef(const char *name, ostream& os=cout);
  virtual Sexpression *ACL2Assign(Expression *rval);
  virtual uint ACL2ValWidth();
  virtual Sexpression *ACL2Eval(Sexpression *s);
};

class PrimType : public Symbol, public Type {
public:
  char *RACname;
  PrimType(const char *s, const char *m=NULL);
  virtual bool isPrimType();
  bool isIntegerType();
  void display(ostream& os);
};

extern PrimType boolType;
extern PrimType intType;
extern PrimType uintType;
extern PrimType int64Type;
extern PrimType uint64Type;

class DefinedType : public Symbol, public Type {
public:
  Type *def;
  Type *derefType();
  DefinedType(const char *s, Type *t);
  void display(ostream& os);
  void displayDef(ostream& os=cout);
};

class RegType : public Type {
public:
  RegType(Expression *w);
  Expression *width;
  bool isRegType();
  virtual bool isSigned();
  Sexpression *ACL2Assign(Expression *rval);
};

class UintType : public RegType {
public:
  UintType(Expression *w);
  bool isIntegerType();
  void display(ostream& os=cout);
  uint ACL2ValWidth();
};

class IntType : public RegType {
public:
  bool isSigned();
  IntType(Expression *w);
  bool isIntegerType();
  void display(ostream& os=cout);
  Sexpression *ACL2Eval(Sexpression *s);
};

class FPType :public RegType {
public:
  Expression *iwidth;
  FPType(Expression *w, Expression *iw);
  bool isFPType();
  bool isIntegerType();
  Sexpression *ACL2Assign(Expression *rval);
};

class UfixedType :public FPType {
public:
  UfixedType(Expression *w, Expression *iw);
  void display(ostream& os=cout);
  Sexpression *ACL2Eval(Sexpression *s);
};

class FixedType :public FPType {
public:
  bool isSigned();
  FixedType(Expression *w, Expression *iw);
  void display(ostream& os=cout);
  Sexpression *ACL2Eval(Sexpression *s);
};

class ArrayType : public Type {
public:
  Type *baseType;
  Expression *dim;
  ArrayType(Expression *d, Type *t);
  Type *getBaseType();
  bool isArrayType();
  void display(ostream& os);
  void displayVarType(ostream& os=cout);
  void displayVarName(const char *name, ostream& os=cout);
  void makeDef(const char *name, ostream& os);
};

class ArrayParamType : public ArrayType {
public:
  ArrayParamType(Expression *d, Type *t);
  bool isArrayParamType();
  void display(ostream& os);
  void displayVarType(ostream& os=cout);
  void displayVarName(const char *name, ostream& os=cout);
  void makeDef(const char *name, ostream& os);
};

class StructField {
public:
  Symbol *sym;
  Type *type;
  StructField(Type *t, char *n);
  char *getname();
  void display(ostream& os, uint indent=0);
};

class StructType : public Type {
public:
  List<StructField> *fields;
  StructType(List<StructField> *f);
  bool isStructType();
  void displayFields(ostream& os);
  void display(ostream& os);
  void makeDef(const char *name, ostream& os=cout);
};

class Expression;

class SymDec {
public:
  Symbol* sym;
  Type *type;
  Expression *init;
  SymDec(const char *n, Type *t, Expression *i = NULL);
  char *getname();
  void displaySymDec(ostream& os);
  virtual bool isGlobal();
  virtual bool isROM();
  virtual bool isConst();
  virtual int evalConst();
  virtual Sexpression *ACL2SymExpr();
};

class EnumConstDec : public SymDec {
public:
  EnumConstDec(const char *n, Expression *v=NULL);
  void display(ostream& os);
  bool isConst();
  Sexpression *ACL2Expr();
  Sexpression *ACL2SymExpr();
};

class EnumType : public Type {
public:
  List<EnumConstDec> *vals;
  EnumType(List<EnumConstDec> *v);
  bool isEnumType();
  bool isIntegerType();
  void displayConsts(ostream& os);
  void display(ostream& os);
  void makeDef(const char *name, ostream& os=cout);
  Sexpression *ACL2Expr();
  Sexpression *getEnumVal(Symbol *s);
};

class MvType : public Type {
public:
  uint numVals;
  Type *type[8];
  MvType(uint n, Type *t0, Type *t1, Type *t2 = NULL, Type *t3 = NULL, Type *t4 = NULL, Type *t5 = NULL, Type *t6 = NULL, Type *t7 = NULL);
  void display(ostream& os);
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
  void display(ostream& os);
  virtual void displayNoParens(ostream& os) = 0;
  virtual Expression *subst(SymRef *var, Expression *val);
  virtual Sexpression *ACL2Expr(bool isBV = false);
  virtual Sexpression *ACL2ArrayExpr();
  virtual Sexpression *ACL2Assign(Sexpression *rval);
  virtual uint ACL2ValWidth();
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
  bool isInteger();
  void displayNoParens(ostream& os);
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
  bool isInteger();
  void displayNoParens(ostream& os);
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
  bool isInteger();
  Type* exprType();
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class Template;

class TempCall : public FunCall {
public:
  Symbol *instanceSym;
  List<Expression> *params;
  TempCall(Template *f, List<Expression> *a, List<Expression> *p);
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class Initializer : public Expression {
public:
  List<Constant> *vals;
  Initializer(List<Constant> *v);
  bool isInitializer();
  void displayNoParens(ostream& os);
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
  bool isInteger();
  Type* exprType();
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
};

class ArrayParamRef : public ArrayRef {
public:
  ArrayParamRef(Expression *a, Expression *i);
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
};

class StructRef : public Expression {
public:
  Expression *base;
  char *field;
  StructRef(Expression *s, char *f);
  bool isArray();
  bool isArrayParam();
  bool isInteger();
  Type* exprType();
  void displayNoParens(ostream& os);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
};

class BitRef : public Expression {
public:
  Expression *base;
  Expression *index;
  BitRef(Expression *b, Expression *i);
  bool isInteger();
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
  uint ACL2ValWidth();
};

class Subrange : public Expression {
public:
  Expression *base;
  Expression *high;
  Expression *low;
  uint width;
  Subrange(Expression *b, Expression *h, Expression *l);
  Subrange(Expression *b, Expression *h, Expression *l, uint w);
  bool isSubrange();
  bool isInteger();
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
  Sexpression *ACL2Assign(Sexpression *rval);
  uint ACL2ValWidth();
};

class PrefixExpr : public Expression {
public:
  Expression *expr;
  const char *op;
  PrefixExpr(Expression *e, const char *o);
  bool isConst();
  int evalConst();
  bool isInteger();
  void displayNoParens(ostream& os);
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
  bool isInteger();
  void displayNoParens(ostream& os);
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
  bool isInteger();
  void displayNoParens(ostream& os);
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
  bool isInteger();
  void displayNoParens(ostream& os);
  Expression *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr(bool isBV = false);
};

class MultipleValue : public Expression {
public:
  MvType *type;
  Expression *expr[8];
  MultipleValue(MvType *t, Expression **e);
  MultipleValue(MvType *t, List<Expression> *e);
  void displayNoParens(ostream& os);
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
  virtual void display(ostream& os, uint indent=0) = 0;
  virtual void displayAsRightBranch(ostream& os, uint indent=0);
  virtual void displayWithinBlock(ostream& os, uint indent=0);
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
  void display(ostream& os, uint indent=0);
  virtual void displaySimple(ostream& os) = 0;
};

class VarDec : public SimpleStatement, public SymDec {
public:
  VarDec(const char *n, Type *t, Expression *i = NULL);
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
  Assignment(Expression *l, const char *o, Expression *r=NULL);
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
  uint width;
  Expression *val;
  AssignFull(Expression *b, uint w, Expression *v);
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
  void display(ostream& os, uint indent=0);
  void displayWithinBlock(ostream& os, uint indent=0);
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
  void display(ostream& os, uint indent=0);
  void displayAsRightBranch(ostream& os, uint indent=0);
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
  void display(ostream& os, uint indent=0);
  Statement *subst(SymRef *var, Expression *val);
  Sexpression *ACL2Expr();
  void markAssertions(FunDef *f);
};

class Case {
public:
  Expression *label;
  List<Statement> *action;
  Case(Expression *l, List<Statement> *a);
  void display(ostream& os, uint indent=0);
  Case* subst(SymRef *var, Expression *val);
  void markAssertions(FunDef *f);
};

class SwitchStmt : public Statement {
public:
  Expression *test;
  List<Case> *cases;
  SwitchStmt(Expression *t, List<Case> *c);
  void display(ostream& os, uint indent=0);
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
  uint arity();
  char *getname();
  void displayDec(ostream& os, uint indent=0);
  virtual void display(ostream& os, const char *prefix = "", uint indent=0);
  virtual void displayACL2Expr(ostream& os);
};

class Builtin : public FunDef {
public:
  Builtin(const char *n, Type *t, Type *a0=NULL, Type *a1=NULL, Type *a2=NULL);
};

class Template : public FunDef{
public:
  List<TempParamDec> *tempParams;
  List<TempCall> *calls;
  Template(const char *n, Type *t, List<VarDec> *p, Block *b, List<TempParamDec> *tp);
  void display(ostream& os, const char *prefix = "", uint indent=0);
  void addCall(TempCall *c);
  void bindParams(List<Expression> *a);
  void displayACL2Expr(ostream& os);
};

//***********************************************************************************
// Programs
//***********************************************************************************

enum DispMode {rac, acl2};

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
  void display(ostream& os, DispMode mode=rac);
};

extern Program prog;

#endif
