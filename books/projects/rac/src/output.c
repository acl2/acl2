#include "parser.h"

// 6/27/18
// I just eliminated two features that are no longer used: (1) CtoS mode, in which a
// program was printed in a form acceptable to CtoS, and (2) SystemC registers, which
// have been replaced by those of Algorithmic C, hence the change in the name of the
// entire system from MASC (Modeling Algorithms in SystemC) to RAC (Restricted
// Algorithmic C).  This simplified the parser considerably, and I suspect I've left
// a bunch of dead or useless code lying around, to be dealt with later.

//***********************************************************************************
// S-expressions
//***********************************************************************************

// An Sexpression is a Symbol, a Cons, or a Plist (proper list of S-expressions).
// Note that Constant is a derived class of Symbol.

// class Plist : public Sexpression
// --------------------------------

// Data member:  List<Sexpression> *list;


Plist::Plist(Sexpression *s) {
  list = new List<Sexpression>(s);
}

Plist::Plist(Sexpression *s1, Sexpression* s2) {
  list = (new List<Sexpression>(s2))->push(s1);
}

Plist::Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3) {
  list = (new List<Sexpression>(s3))->push(s2)->push(s1);
}

Plist::Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4) {
  list = (new List<Sexpression>(s4))->push(s3)->push(s2)->push(s1);
}

Plist::Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5) {
  list = (new List<Sexpression>(s5))->push(s4)->push(s3)->push(s2)->push(s1);
}

Plist::Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5, Sexpression* s6) {
  list = (new List<Sexpression>(s6))->push(s5)->push(s4)->push(s3)->push(s2)->push(s1);
}

Plist::Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5, Sexpression* s6, Sexpression* s7) {
  list = (new List<Sexpression>(s7))->push(s6)->push(s5)->push(s4)->push(s3)->push(s2)->push(s1);
}

Plist::Plist(Sexpression *s1, Sexpression* s2, Sexpression* s3, Sexpression* s4, Sexpression* s5, Sexpression* s6, Sexpression* s7, Sexpression* s8) {
  list = (new List<Sexpression>(s8))->push(s7)->push(s6)->push(s5)->push(s4)->push(s3)->push(s2)->push(s1);
}

Plist::Plist(List<Sexpression> *l) {list = l;}

Plist *Plist::add(Sexpression *s) {
  if (list) {
    list->add(s);
  }
  else {
    list = new List<Sexpression>(s);
  }
  return this;
}

Plist *Plist::push(Sexpression *s) {
  if (list) {
    list = list->push(s);
  }
  else {
    list = new List<Sexpression>(s);
  }
  return this;
}

void Plist::display(ostream& os) {
  os << "(";
  if (list) {
    list->value->display(os);
    List<Sexpression> *rest = list->next;
    while (rest) {
      os << " ";
      rest->value->display(os);
      rest = rest->next;
    }
  }
  os << ")";
}

// class Cons : public Sexpression (used in Initializer::ACL2ArrayExpr())
// ----------------------------------------------------------------------

// Data members:
//   Sexpression *car;
//   Sexpression *cdr;

Cons::Cons(Sexpression *a, Sexpression *d) {car = a; cdr = d;}

void Cons::display(ostream& os) {
   os << "(";
   car->display(os);
   os << " . ";
   cdr->display(os);
   os << ")";
}

// class Symbol : public Sexpression
// ---------------------------------

// Data member: char *name;

Symbol::Symbol(const char *s) {
  name = new char[strlen(s)+1];
  strcpy(name, s);
}

Symbol::Symbol(int n) {
  ostringstream ostr;
  ostr << n;
/*
The following line gave me big problems because it creates a pointer
that outlives the object to which it points:
  const char *s = ostr.str().c_str();
*/
  string st = ostr.str();
  const char *s = st.c_str();
  name = new char[strlen(s)+1];
  strcpy(name, s);
}

Symbol::~Symbol() {delete[] name;}

char *Symbol::getname() {return name;}

void Symbol::display(ostream& os) {os << name;}

// Symbol constants used in translation:

Symbol s_ag("ag");
Symbol s_as("as");
Symbol s_ash("ash");
Symbol s_assert("assert");
Symbol s_assign("assign");
Symbol s_bitn("bitn");
Symbol s_bits("bits");
Symbol s_block("block");
Symbol s_break("break");
Symbol s_case("case");
Symbol s_declare("declare");
Symbol s_default("default");
Symbol s_divide("/");
Symbol s_expt("expt");
Symbol s_fl("fl");
Symbol s_false("false$");
Symbol s_true("true$");
Symbol s_funcdef("funcdef");
Symbol s_if("if");
Symbol s_if1("if1");
Symbol s_for("for");
Symbol s_list("list");
Symbol s_logand("logand");
Symbol s_logand1("logand1");
Symbol s_logeq("log=");
Symbol s_loggeq("log>=");
Symbol s_loggreater("log>");
Symbol s_logior("logior");
Symbol s_logior1("logior1");
Symbol s_logleq("log<=");
Symbol s_logless("log<");
Symbol s_logneq("log<>");
Symbol s_lognot("lognot");
Symbol s_lognot1("lognot1");
Symbol s_logxor("logxor");
Symbol s_minus("-");
Symbol s_mv("mv");
Symbol s_mv_assign("mv-assign");
Symbol s_nth("nth");
Symbol s_null("null");
Symbol s_plus("+");
Symbol s_quote("quote");
Symbol s_rem("rem");
Symbol s_return("return");
Symbol s_t("t");
Symbol s_times("*");
Symbol s_floor("floor");
Symbol s_setbitn("setbitn");
Symbol s_setbits("setbits");
Symbol s_si("si");
Symbol s_switch("switch");
Symbol s_temp[4] = {Symbol("temp-0"), Symbol("temp-1"), Symbol("temp-2"), Symbol("temp-3")};


// class SymDec (symbol declaration)
// ------------

// Derived classes: EnumConstDec, VarDec, and TempParamDec.

// Data members: Symbol* sym; Type *type; Expression *init; (init is optional)

SymDec::SymDec(const char *n, Type *t, Expression *i) {
  sym = new Symbol(n); type = t; init = i;
}

char *SymDec::getname() {return sym->name;}

void SymDec::displaySymDec(ostream& os) {
  type->displayVarType(os);
  os << " ";
  type->displayVarName(getname(), os);
  if (init) {
    os << " = ";
    init->display(os);
  }
}

bool SymDec::isConst() {return false;} // overridden by EnumConstDec and ConstDec

int SymDec::evalConst() {assert(init); return init->evalConst();}

bool SymDec::isGlobal() {return false;}

bool SymDec::isROM() {return false;}

Sexpression *SymDec::ACL2SymExpr() {// Sexpression for a reference to this symbol.
  assert(!"Undefined method: ACL2SymExpr");
  return NULL;
}


//***********************************************************************************
// class Type
//***********************************************************************************

// Derived classes:

//   PrimType           (primitive type: uintTYpe, intType, boolType)
//   DefinedType        (introduced by typedef)
//   RegType            (Algorithmic C register type)
//     UintType         (unsigned limited integer register)
//     IntType          (signed limited integer register)
//     FPType           (fixed-point register
//       UfixedType     (unsigned fixed-point register
//       FixedType      (signed fixed-point register
//   ArrayType          (array type)
//     ArrayParamType   (array template class, which may be passed as parameter)
//   StructType         (struct type)
//   EnumType           (enumeration type)
//   MvType             (multiple value type)

bool Type::isPrimType() {return false;}  // virtual (overridden by PrimType)

bool Type::isRegType() {return false;}  // virtual (overridden by RegType)

bool Type::isFPType() {return false;} // virtual (overridden by FPType)

bool Type::isArrayType() {return false;}  // virtual (overridden by ArrayType)

bool Type::isArrayParamType() {return false;}  // virtual (overridden by ArrayParamType)

bool Type::isStructType() {return false;}  // virtual (overridden by StructType)

bool Type::isEnumType() {return false;} // virtual (overridden by EnumType)

bool Type::isNumericalType() {return isPrimType() || isRegType() || isEnumType();}

bool Type::isIntegerType() {return false;} // virtual (overridden by integer types)

Type *Type::derefType() {return this;} // virtual (overridden by DefinedType)

void Type::display(ostream& os) {assert("!Undefined method: display");}

void Type::displayVarType(ostream& os) { // virtual (overridden by ArrayType)
  // How this type is displayed in a variable declaration
  display(os);
}

void Type::displayVarName(const char *name, ostream& os) { // virtual (overridden by ArrayType)
  // How a variable of this type is displayed in a variable declaration
  os << name;
}

void Type::makeDef(const char *name, ostream& os) { // virtual (overridden by ArrayType, StructType, and EnumType)
  // How this type is displayed in a type definition.
  os << "\ntypedef ";
  display(os);
  os << " " << name << ";";
}

uint Type::ACL2ValWidth() { // virtual (overridden by UintType)
  // Boundary on the width of the value of an object of this type.
  // 0 indicates unknown or unbounded width.
  // Used to avoid unnecessary call to bits.
  return 0;
}

Sexpression *Type::ACL2Assign(Expression *rval) { // virtual (overridden by RegType)
  // Convert rval to an S-expression to be assigned to an object of this type.
  return rval->ACL2Expr();
}

Sexpression *Type::ACL2Eval(Sexpression *s) { // virtual (overridden by RegType)
  // For a RegType, the numerical value represented by a given bit vector s.
  // For any other type, just return s.
  return s;
}


// class PrimType : public Symbol, public Type (Primitive type)
// ------------------------------------------------------------

PrimType::PrimType(const char *s, const char *m) : Symbol(s) {
  if (m) {
    RACname = new char[strlen(m)+1];
   strcpy(RACname, m);
  }
}

bool PrimType::isPrimType() {return true;}

bool PrimType::isIntegerType() {return true;}

void PrimType::display(ostream& os) {
  if (RACname) {
    os << RACname;
  }
  else {
    Symbol::display(os);
  }
}

PrimType boolType("bool");
PrimType intType("int");
PrimType uintType("uint");
PrimType int64Type("int64", "int");
PrimType uint64Type("uint64", "uint");

// class DefinedType : public Symbol, public Type (type introduced by typedef)
// ---------------------------------------------------------------------------

// Data member: Type *def;

DefinedType::DefinedType(const char *s, Type *t) : Symbol(s) {def = t;}

Type *DefinedType::derefType() {return def->derefType();}

void DefinedType::display(ostream& os) {Symbol::display(os);}

void DefinedType::displayDef(ostream& os) {
  if (!(def->isRegType())) {
    def->makeDef(name, os);
  }
}


// class RegType : public Type (Algorithmic C register type)
// ---------------------------------------------------

// Data member:  Expression *width

RegType::RegType(Expression *w) {width = w;}

bool RegType::isRegType() {return true;}

bool RegType::isSigned() {return false;} // virtual

Sexpression *RegType::ACL2Assign(Expression *rval) { // overridden by FPType
  Type *t = rval->exprType();
  uint w = rval->ACL2ValWidth();
  if ((t == this) || (w && w <= width->evalConst())) {
    return rval->ACL2Expr(true);
  }
  else {
    Sexpression *s = rval->ACL2Expr();
    if (rval->isFP()) s = new Plist(&s_fl, s);
    return new Plist(&s_bits, s, new Integer(width->evalConst() - 1), &i_0);
  }
}


// class UintType : public RegType
// -------------------------------

UintType::UintType(Expression *w) : RegType(w) {}

bool UintType::isIntegerType() {return true;}

void UintType::display(ostream& os) {
  os << "sc_uint<";
  width->displayNoParens(os);
  os << ">";
}

uint UintType::ACL2ValWidth() {return width->evalConst();}


// class IntType : public RegType
// ------------------------------

bool IntType::isSigned() {return true;}

IntType::IntType(Expression *w) : RegType (w) {}

bool IntType::isIntegerType() {return true;}

void IntType::display(ostream& os) {
  os << "sc_int<";
  width->displayNoParens(os);
  os << ">";
}

Sexpression *IntType::ACL2Eval(Sexpression *s) {
  return new Plist(&s_si, s, new Integer(width->evalConst()));
}


// class FPType :public RegType
// ----------------------------

// Data member:  Expression *iwidth

FPType::FPType(Expression *w, Expression *iw) : RegType (w) {iwidth = iw;}

bool FPType::isFPType() {return true;}

bool FPType::isIntegerType() {return false;}

Sexpression *FPType::ACL2Assign(Expression *rval) {
  Type *t = rval->exprType();
  uint w = rval->ACL2ValWidth();
  if (t == this) {
    return rval->ACL2Expr(true);
  }
  else {
    Sexpression *s = rval->ACL2Expr();
    int wVal = width->evalConst(), iwVal = iwidth->evalConst();
    s = new Plist(&s_times, s, new Plist(&s_expt, &i_2, new Integer(wVal - iwVal)));
    if ((rval->isFP()) || wVal < iwVal) s = new Plist(&s_fl, s);
    return new Plist(&s_bits, s, new Integer(wVal - 1), &i_0);
  }
}


// class UfixedType : public FPType
// ---------------------------------

UfixedType::UfixedType(Expression *w, Expression *iw) : FPType (w, iw) {}

void UfixedType::display(ostream& os) {
  os << "sc_ufixed<";
  width->displayNoParens(os);
  os << ", ";
  iwidth->displayNoParens(os);
  os << ">";
}

Sexpression *UfixedType::ACL2Eval(Sexpression *s) {
  return new Plist(&s_divide, s, new Plist(&s_expt, &i_2, new Integer(width->evalConst() - iwidth->evalConst())));
}

// class FixedType : public RegType
// --------------------------------

FixedType::FixedType(Expression *w, Expression *iw) : FPType (w, iw) {}

bool FixedType::isSigned() {return true;}

void FixedType::display(ostream& os) {
  os << "sc_fixed<";
  width->displayNoParens(os);
  os << ", ";
  iwidth->displayNoParens(os);
  os << ">";
}

Sexpression *FixedType::ACL2Eval(Sexpression *s) {
  Sexpression *numerator = new Plist(&s_si, s, new Integer(width->evalConst()));
  Sexpression *denominator = new Plist(&s_expt, &i_2, new Integer(width->evalConst() - iwidth->evalConst()));
  return new Plist(&s_divide, numerator, denominator);
}

// class ArrayType : public Type
// -----------------------------

// Data members: Type *baseType; Expresion *dim;


ArrayType::ArrayType(Expression *d, Type *t) {
  baseType = t;
  dim = d;
}

Type *ArrayType::getBaseType() {return baseType->derefType();}

bool ArrayType::isArrayType() {return true;}

void ArrayType::display(ostream& os) {
  baseType->display(os);
  os << "[";
  dim->displayNoParens(os);
  os << "]";
}

void ArrayType::displayVarType(ostream& os) {
  baseType->display(os);
}

void ArrayType::displayVarName(const char *name, ostream& os) {
  os << name << "[";
  dim->displayNoParens(os);
  os << "]";
}

void ArrayType::makeDef(const char *name, ostream& os) {
  Type *b = baseType;
  List<Expression> *dims = new List<Expression>(dim);
  while (b->isArrayType() && !(b->isArrayParamType())) {
    dims = dims->push(((ArrayType*)b)->dim);
    b = ((ArrayType*)b)->baseType;
  }
  os << "\ntypedef ";
  b->display(os);
  os << " " << name;
  while (dims) {
    os << "[";
    (dims->value)->displayNoParens(os);
    os << "]";
    dims = dims->next;
  }
  os << ";";
}

// class ArrayParamType : public ArrayType (array template type)
// -------------------------------------------------------------

ArrayParamType::ArrayParamType(Expression *d, Type *t) : ArrayType(d, t) {}

void ArrayParamType::display(ostream& os) {
  ArrayType::display(os);
}

bool ArrayParamType::isArrayParamType() {return true;}

void ArrayParamType::displayVarType(ostream& os) {
  ArrayType::displayVarType(os);
}

void ArrayParamType::displayVarName(const char *name, ostream& os) {
  ArrayType::displayVarName(name, os);
}

void ArrayParamType::makeDef(const char *name, ostream& os) {
  ArrayType::makeDef(name, os);
}


// class StructField
// -----------------

// Data members:  Symbol *sym; Type *type;

StructField::StructField(Type *t, char *n) {sym = new Symbol(n); type = t;}

char *StructField::getname() {return sym->name;}

void StructField::display(ostream& os, uint indent) {
  if (indent) {os << setw(indent) << " ";}
  type->display(os);
  os << " " << getname() << ";";
}

// class StructType : public Type
// ------------------------------

// Data member:  List<StructField> *fields;

StructType::StructType(List<StructField> *f) {fields = f;}

bool StructType::isStructType() {return true;}

void StructType::displayFields(ostream& os) {
  os << "{";
  List<StructField> *ptr = fields;
  while (ptr) {
    ptr->value->display(os);
    if (ptr->next) os << " ";
    ptr = ptr->next;
  }
  os << "}";
}

void StructType::display(ostream& os) {
    os << "struct ";
    this->displayFields(os);
}

void StructType::makeDef(const char *name, ostream& os) {
  os << "\nstruct " << name << " ";
  displayFields(os);
  os << ";";
}

// class EnumConstDec : public SymDec
// ----------------------------------

EnumConstDec::EnumConstDec(const char *n, Expression *v) : SymDec(n, &intType, v) {}

void EnumConstDec::display(ostream& os) {
  os << getname();
  if (init) {
    os << "=";
    init->display(os);
  }
}

bool EnumConstDec::isConst() {return true;}

Sexpression *EnumConstDec::ACL2Expr() {
  if (init) {
    return new Plist(sym, init->ACL2Expr());
  }
  else {
    return sym;
  }
}

Sexpression *EnumConstDec::ACL2SymExpr() {
  return ((EnumType*)type)->getEnumVal(sym);
}

// class EnumType : public Type
// ----------------------------

// Data member:  List<EnumConstDec> *vals;

EnumType::EnumType(List<EnumConstDec> *v) {
  vals = v;
  while (v) {
    v->value->type = this;
    v = v->next;
  }
}

Sexpression *EnumType::ACL2Expr() {
  Plist *result = new Plist();
  List<EnumConstDec> *v = vals;
  while (v) {
    result->add(v->value->ACL2Expr());
    v = v->next;
  }
  return result;
}

bool EnumType::isIntegerType() {return true;}

bool EnumType::isEnumType() {return true;}

void EnumType::displayConsts(ostream& os) {
  os << "{";
  List<EnumConstDec> *ptr = vals;
  while (ptr) {
    ptr->value->display(os);
    if (ptr->next) os << ", ";
    ptr = ptr->next;
  }
  os << "}";
}

void EnumType::display(ostream& os) {
  os << "enum ";
  displayConsts(os);
}

Sexpression *EnumType::getEnumVal(Symbol *s) {
  List<EnumConstDec> *ptr = vals;
  uint count = 0;
  while (ptr) {
    if (ptr->value->init) {
      count = ptr->value->init->evalConst();
    }
    if (ptr->value->sym == s) {
      return new Integer(count);
    }
    else {
      count++;
      ptr = ptr->next;
    }
  }
  assert(!"enum constant not found");
  return 0;
}

void EnumType::makeDef(const char *name, ostream& os) {
  os << "\nenum " << name << " ";
  displayConsts(os);
  os << ";";
}

// class MvType : public Type (multiple-value type)
// -------------------------------------------

// Data members:  uint numVals; Type *type[8];
// 2 <= numVals <= 8; determines number of valid entries of type[].

MvType::MvType(uint n, Type *t0, Type *t1, Type *t2, Type *t3, Type *t4, Type *t5, Type *t6, Type *t7) {
  numVals = n;
  type[0] = t0;
  type[1] = t1;
  type[2] = t2;
  type[3] = t3;
  type[4] = t4;
  type[5] = t5;
  type[6] = t6;
  type[7] = t7;
}

void MvType::display(ostream& os) {
  os << "<";
  type[0]->display(os);
  os << ", ";
  type[1]->display(os);
  if (type[2]) {
    os << ", ";
    type[2]->display(os);
    if (type[3]) {
      os << ", ";
      type[3]->display(os);
      if (type[4]) {
        os << ", ";
        type[4]->display(os);
	if (type[5]) {
          os << ", ";
          type[5]->display(os);
	  if (type[6]) {
            os << ", ";
            type[6]->display(os);
	    if (type[7]) {
	      os << ", ";
	      type[7]->display(os);
	    }
  	  }
	}
      }
    }
  }
  os << ">";
}


//***********************************************************************************
// class Expression
//***********************************************************************************

// Derived classes:

//   Constant            (also derived class of Symbol)
//     Integer
//     Boolean
//   SymRef              (Reference to declared symbol, i.e., enum constant or variable)
//   Funcall             (function call)
//   Initializer         (initial value of array, a list of constants)
//   ArrayRef            (array reference)
//     ArrayParamRef
//   StructRef           (struct field reference)
//   BitRef              (bit extraction)
//   Subrange            (subrange extraction)
//   PrefixExpr          (application of unary operator)
//   CastExpr
//   BinaryExpr          (application of binary operator)
//   CondExpr            (conditional expression, _ ? _ : _)
//   MultipleValue       (used only as return values of functions)

// Data member:  bool needsParens; (printed within parentheses in the source code)

Expression::Expression() {needsParens = false;}

bool Expression::isSymRef() {return false;} // virtual

bool Expression::isConst() {return false;} // virtual

// Value of expression, applicable to a limited variety of integer-valued constant expressions:

int Expression::evalConst() { // virtual (overridden by constant expressions)
  assert(!"attempt to evaluate a non-constant expression");
  return 0;
}

bool Expression::isArray() {return false;} // virtual

bool Expression::isArrayParam() {return false;} // virtual

bool Expression::isStruct() {return false;} // virtual

bool Expression::isNumber() {return !isArray() && !isStruct();}

bool Expression::isSubrange() {return false;} // virtual

bool Expression::isInteger() { // virtual
  return false;
}

bool Expression::isFP() {return isNumber() && !isInteger();}

// The following expressions have associated types: variable, array, and struct references;
// function calls; cast expressions; applications of "~" to typed expressions; and applications
// of "&", "|", and "^" to typed expressions of the same type.  For all other expressions,
// exprType is undefined:

Type* Expression::exprType() { // virtual (overridden by SymRef, Funcall, ArrayRef, StructRef, PrefixExpr, and BinaryExpr)
  // Dereferenced type of expression.
  return NULL;
}

// displayNoParens is defined for each class of expressions and is called by the non-virtual
// display method, which inserts parentheses as required:

// virtual void displayNoParens(ostream& os) = 0;

void Expression::display(ostream& os) {
  if (needsParens) os << "(";
  displayNoParens(os);
  if (needsParens) os << ")";
}

// The following method substitutes each occurrence of a given variable with a given value:

Expression *Expression::subst(SymRef *var, Expression *val) { // virtual
  return this;
}

// The following method converts an expression to an S-expression.  The argument isBV is relevant
// only for a typed expression of a register type (see exprType above).  In this case, if isBV is
// true, then the resulting S-expression should represent the value of the bit vector contents
// of the register, and otherwise it should represent the value of that bit vector as interpreted
// according to the type. The argument isBV is set the following cases:
// (1) The expression is being assigned to a register of the same type;
// (2) The expression is being assigned to an integer register and the expression is an unsigned
//     integer register of width not exceeding that of the target;
// (3) The resulting S-expression is to be the first argument of bitn, bits, setbitn, or setbits.
// (4) The expression is an argument of a logical expression of a register type.

Sexpression *Expression::ACL2Expr(bool isBV) { // virtual
  assert(!"Expression cannot be converted to an S-expression");
  return NULL;
}

// The following method converts an expression to an Sexpression to be used as an array initialization.
// It returns the same value as ACL2Expr, except for an Initializer:

Sexpression *Expression::ACL2ArrayExpr() { // virtual (overridden by Initializer)
  return ACL2Expr();
}

// Translate to an ACL2 assignment with this lvalue and the rvalue given as the argument:

Sexpression *Expression::ACL2Assign(Sexpression *rval) { // virtual (overridden by valid lvalues)
  assert(!"Assigment can be made only to an expression of type SymRef, ArrayRef, StructRef, BitRef, or Subrange");
  return NULL;
}

// If a numerical expression is known to have a non-negative value of bounded width, then return
// the bound; otherwise, return 0:

uint Expression::ACL2ValWidth() { // virtual (overridden by BitRef and Subrange)
  Type *t = exprType();
  return t ? t->ACL2ValWidth() : 0;
}

// The remaining Expression methods are defined solely for the purpose of making ACL2ValWidth
// a little smarter by computing the width of a Subrange expression when the limits differ by a
// computable constant:

bool Expression::isPlusConst(Expression *e) { // virtual (overridden by BinaryExpr)
  // Used only by Subrange::ACL2ValWidth
  // Applied to the upper limit of a Subrange expression to determine whether it is
  // it is a binary expression representing the sum of the lower limit and a constant.
  return false;
}

bool Expression::isEqual(Expression *e) { // virtual (overridden by PrefixExpr and BinaryExpr)
  // Is this expression known to be equal in value to e?
  // Used only by isPlusConst.
  return this == e;
}

bool Expression::isEqualPrefix(const char *o, Expression *e) { // virtual (overridden by PrefixExpr)
  // Is this a prefix expression with the given operator and argument?
  // Used only by isEqual.
  return false;
}

bool Expression::isEqualBinary(const char *o, Expression *e1, Expression *e2) { // virtual (overridden by BinaryExpr)
  // Is this a binary expression with the given operator and arguments?
  // Used only by isEqual.
  return false;
}

bool Expression::isEqualConst(Constant *c) { // virtual (overridden by Constant)
  // Is this a constant equal to a given constant?
  // Used only by isEqual.
  return false;
}

bool Expression::isEqualSymRef(SymDec *s) { // virtual (overridden by SymRef)
  // Is this a reference to a given symbol?
  // Used only by isEqual.
  return false;
}

int Expression::getPlusConst() { // virtual (overridden by BinaryExpr)
  // Called on a binary expression for which isPlusConst is true; returns the value of the constant.
  return 0;
}


// class Constant : public Expression, public Symbol
// -------------------------------------------------

Constant::Constant(const char *n) : Expression(), Symbol(n) {}

Constant::Constant(int n) : Expression(), Symbol(n) {}

bool Constant::isConst() {return true;}

bool Constant::isInteger() {return true;}

void Constant::displayNoParens(ostream& os) {os << name;}

Sexpression *Constant::ACL2Expr(bool isBV) {return this;}

bool Constant::isEqual(Expression *e) {
  return e->isEqualConst(this);
}

bool Constant::isEqualConst(Constant *c) {
  return !strcmp(name, c->name);
}


// class Integer : public Constant
// -------------------------------

Integer::Integer(const char *n) : Constant(n) {}

Integer::Integer(int n) : Constant(n) {}

int Integer::evalConst() {
  if (!strncmp(name, "0x", 2)) {
    return strtol(name+2, NULL, 16);
  }
  else if (!strncmp(name, "-0x", 3)) {
    return -strtol(name+3, NULL, 16);
  }
  else {
    return atoi(name);
  }
}

Sexpression *Integer::ACL2Expr(bool isBV) {
  if (!strncmp(name, "0x", 2)) {
    Symbol *result = new Symbol(name);
    result->name[0] = '#';
    return result;
  }
  else if (!strncmp(name, "-0x", 3)) {
    Symbol *result = new Symbol(name+1);
    result->name[0] = '#';
    return new Plist(&s_minus, result);
  }
  else {
    return this;
  }
}

Integer i_0("0");
Integer i_1("1");
Integer i_2("2");


// class Boolean : public Constant
// -------------------------------
Boolean::Boolean(const char *n) : Constant(n) {}

int Boolean::evalConst() {
  if (!strcmp(name, "true")) return 1;
  else if (!strcmp(name, "false")) return 0;
  else assert(false);
}

Boolean b_true("true");
Boolean b_false("false");

Sexpression *Boolean::ACL2Expr(bool isBV) {
  if (!strcmp(name, "true")) return new Plist(&s_true);
  else if (!strcmp(name, "false")) return new Plist(&s_false);
  else cout << name << endl; assert(false);
}


// class SymRef : public Expression
// ---------------------------------------------------------------

// Reference to declared symbol, which may be an enumeration constant or a variable

// Data member: SymDec *symDec;

SymRef::SymRef(SymDec *s) : Expression() {symDec = s;}

bool SymRef::isSymRef() {return true;}

Type* SymRef::exprType() {return symDec->type->derefType();}

bool SymRef::isConst() {return symDec->isConst();}

int SymRef::evalConst() {
  if (isConst()) {
    return symDec->evalConst();
  }
  else {
    assert(!"Attempt to evaluate a non-constant symbol reference.");
  }
}

bool SymRef::isArray() {return exprType()->isArrayType();}

bool SymRef::isArrayParam() {return exprType()->isArrayParamType();}

bool SymRef::isStruct() {return exprType()->isStructType();}

bool SymRef::isInteger() {return exprType()->isIntegerType();}

void SymRef::displayNoParens(ostream& os) {symDec->sym->display(os);}

Expression *SymRef::subst(SymRef *var, Expression *val) {
  return (symDec == var->symDec) ? val : (Expression*)this;
}

Sexpression *SymRef::ACL2Expr(bool isBV) {
  Sexpression *s = symDec->ACL2SymExpr();
  return isBV ? s : exprType()->ACL2Eval(s);
}

Sexpression *SymRef::ACL2Assign(Sexpression *rval) {
  return new Plist(&s_assign, symDec->sym, rval);
}

bool SymRef::isEqual(Expression *e) {
  return e->isEqualSymRef(symDec);
}

bool SymRef::isEqualSymRef(SymDec *s) {
  return s == symDec;
}

// class FunCall : public Expression (function call)
// -------------------------------------------------

// Data members:  FunDef *func; List<Expression> *args;


FunCall::FunCall(FunDef *f, List<Expression> *a) : Expression() {func = f; args = a;}

Type* FunCall::exprType() {return func->returnType->derefType();}

bool FunCall::isArray() {return exprType()->isArrayType();}

bool FunCall::isArrayParam() {return exprType()->isArrayParamType();}

bool FunCall::isStruct() {return exprType()->isStructType();}

bool FunCall::isInteger() {return exprType()->isIntegerType();}

void FunCall::displayNoParens(ostream& os) {
  os << func->getname() << "(";
  List<Expression> *ptr = args;
  while (ptr) {
    ptr->value->display(os);
    if (ptr->next) os << ", ";
    ptr = ptr->next;
  }
  os << ")";
}

Expression *FunCall::subst(SymRef *var, Expression *val) {
   List<Expression> *ptr = args;
   List<Expression> *newArgs = NULL;
   while (ptr) {
     Expression *expr = ptr->value->subst(var, val);
     if (newArgs) {
       newArgs->add(expr);
     }
     else {
       newArgs = new List<Expression>(expr);
     }
     ptr = ptr->next;
   }
   return new FunCall(func, newArgs);
}

Sexpression *FunCall::ACL2Expr(bool isBV) {
  Plist *result = new Plist(new Symbol(func->getname()));
  List<VarDec> *p = func->params;
  List<Expression> *a = args;
  while (a) {
    result->add(p->value->type->derefType()->ACL2Assign(a->value));
    a = a->next;
    p = p->next;
  }
  return isBV ? result : exprType()->ACL2Eval(result);
}


// class TempCall : public Expression (function template Data)
// -------------------------------------------------

// call members:  Symbol *instanceSym; List<Expression> *params;

TempCall::TempCall(Template *f, List<Expression> *a, List<Expression> *p) : FunCall(f, a) {
  params = p;
  if (f->calls == NULL) {
    f->calls = new List<TempCall>(this);
  }
  else {
    f->calls->add(this);
  }
}

void TempCall::displayNoParens(ostream& os) {
  os << func->getname() << "<";
  List<Expression> *ptr = params;
  while (ptr) {
    ptr->value->display(os);
    if (ptr->next) os << ", ";
    ptr = ptr->next;
  }
  os << ">(";
  ptr = args;
  while (ptr) {
    ptr->value->display(os);
    if (ptr->next) os << ", ";
    ptr = ptr->next;
  }
  os << ")";
}

Expression *TempCall::subst(SymRef *var, Expression *val) {
  TempCall *result = (TempCall*)FunCall::subst(var, val);
  List<Expression> *ptr = params;
  List<Expression> *newParams = NULL;
  while (ptr) {
    Expression *expr = ptr->value->subst(var, val);
    if (newParams) {
      newParams->add(expr);
    }
    else {
      newParams = new List<Expression>(expr);
    }
    ptr = ptr->next;
  }
  result->params = newParams;
  return result;
}

Sexpression *TempCall::ACL2Expr(bool isBV) {
  ((Template*)func)->bindParams(params);
  Plist *result = (Plist*)FunCall::ACL2Expr(isBV);
  result->list->value = instanceSym;
  return result;
}


// class Initializer : public Expression (array initializer)
// ---------------------------------------------------------

// Data member:  List<Constant> *vals;

Initializer::Initializer(List<Constant> *v) : Expression() {vals = v;}

void Initializer::displayNoParens(ostream& os) {
  os << "{";
  List<Constant> *ptr = vals;
  while (ptr) {
    ptr->value->Symbol::display(os);
    if (ptr->next) os << ", ";
    ptr = ptr->next;
  }
  os << "}";
}

Sexpression *Initializer::ACL2Expr(bool isBV) {
  BigList<Sexpression> *result = new BigList<Sexpression>((Sexpression*)(vals->value->ACL2Expr()));
  List<Constant> *ptr = vals->next;
  while (ptr) {
    result->add((Sexpression*)(ptr->value->ACL2Expr()));
    ptr = ptr->next;
  }
  return new Plist(result->front);
}

Sexpression *Initializer::ACL2ArrayExpr() {
  List<Sexpression> *entries = ((Plist*)(ACL2Expr()))->list;
  Plist *p = new Plist();
  uint i = 0;
  while (entries) {
    if (strcmp(((Constant*)(entries->value))->name, "0")) {
      p->add(new Cons(new Integer(i), entries->value));
    }
    i++;
    entries = entries->next;
  }
  if (p->list) {
    p = new Plist(&s_quote, p);
  }
  return p;
}


// class ArrayRef : public Expression
// ----------------------------------

// Data members:  Expression *array; Expression *index;

ArrayRef::ArrayRef(Expression *a, Expression *i) : Expression() {array = a; index = i;}

Type* ArrayRef::exprType() {return ((ArrayType*)(array->exprType()))->getBaseType();}

bool ArrayRef::isArray() {return exprType()->isArrayType();}

bool ArrayRef::isArrayParam() {return exprType()->isArrayParamType();}

bool ArrayRef::isInteger() {return exprType()->isIntegerType();}

void ArrayRef::displayNoParens(ostream& os) {
  array->display(os);
  os << "[";
  index->display(os);
  os << "]";
}

Expression *ArrayRef::subst(SymRef *var, Expression *val) {
  Expression *newIndex = index->subst(var, val);
  return (newIndex == index) ? this : new ArrayRef(array, newIndex);
}

Sexpression *ArrayRef::ACL2Expr(bool isBV) {
  Sexpression *s;
  if (array->isSymRef() && ((SymRef*)array)->symDec->isROM()) {
    s = new Plist(&s_nth, index->ACL2Expr(), new Plist(((SymRef*)array)->symDec->sym));
  }
  else if (array->isSymRef() && ((SymRef*)array)->symDec->isGlobal()) {
    s = new Plist(&s_ag, index->ACL2Expr(), new Plist(((SymRef*)array)->symDec->sym));
  }
  else {
    s = new Plist(&s_ag, index->ACL2Expr(), array->ACL2Expr());
  }
  return isBV ? s : exprType()->ACL2Eval(s);
}

Sexpression *ArrayRef::ACL2Assign(Sexpression *rval) {
  return array->ACL2Assign(new Plist(&s_as, index->ACL2Expr(), rval, array->ACL2Expr()));
}


// class ArrayParamRef : public ArrayRef
// -------------------------------------

ArrayParamRef::ArrayParamRef(Expression *a, Expression *i) : ArrayRef(a, i) {}

Expression *ArrayParamRef::subst(SymRef *var, Expression *val) {
  Expression *newIndex = index->subst(var, val);
  return (newIndex == index) ? this : new ArrayParamRef(array, newIndex);
}

void ArrayParamRef::displayNoParens(ostream& os) {
  array->display(os);
  os << "[";
  index->display(os);
  os << "]";
}


// class StructRef : public Expression
// -----------------------------------

// Data members:  Expression *base; char *field;

StructRef::StructRef(Expression *s, char *f) : Expression() {base = s; field = f;}

Type* StructRef::exprType() {return ((StructType*)(base->exprType()))->fields->find(field)->type->derefType();}

bool StructRef::isArray() {return exprType()->isArrayType();}

bool StructRef::isArrayParam() {return exprType()->isArrayParamType();}

bool StructRef::isInteger() {return exprType()->isIntegerType();}

void StructRef::displayNoParens(ostream& os) {
  base->display(os);
  os << "." << field;
}

Sexpression *StructRef::ACL2Expr(bool isBV) {
  Symbol *sym = ((StructType*)(base->exprType()))->fields->find(field)->sym;
  Sexpression *s = new Plist(&s_ag, new Plist(&s_quote, sym), base->ACL2Expr());
  return isBV ? s : exprType()->ACL2Eval(s);
}

Sexpression *StructRef::ACL2Assign(Sexpression *rval) {
  Symbol *sym = ((StructType*)(base->exprType()))->fields->find(field)->sym;
  return base->ACL2Assign(new Plist(&s_as, new Plist(&s_quote, sym), rval, base->ACL2Expr()));
}

// class BitRef : public Expression
// --------------------------------

// Data members: Expression *base; Expression *index;

BitRef::BitRef(Expression *b, Expression *i) : Expression() {base = b; index = i;}

bool BitRef::isInteger() {return true;}

void BitRef::displayNoParens(ostream& os) {
  base->display(os);
  os << "[";
  index->display(os);
  os << "]";
}

Expression *BitRef::subst(SymRef *var, Expression *val) {
  Expression *newBase = base->subst(var, val);
  Expression *newIndex = index->subst(var, val);
  return (newBase == base && newIndex == index) ? this : new BitRef(newBase, newIndex);
}

Sexpression *BitRef::ACL2Expr(bool isBV) {
  Sexpression *b = base->ACL2Expr(true);
  Sexpression *i = index->ACL2Expr();
  return new Plist(&s_bitn, b, i);
}

Sexpression *BitRef::ACL2Assign(Sexpression *rval) {
  Sexpression *b = base->ACL2Expr(true);
  Sexpression *i = index->ACL2Expr();
  uint n = (((RegType*)(base->exprType()))->width)->evalConst();
  Integer *s = new Integer(n);
  return base->ACL2Assign(new Plist(&s_setbitn, b, s, i, rval));
}

uint BitRef::ACL2ValWidth() {return 1;}


// class Subrange : public Expression
// ----------------------------------

// Data members: Expression *base; Expression *high; Expression *low;

Subrange::Subrange(Expression *b, Expression *h, Expression *l) : Expression() {
  base = b; high = h; low = l; width = 0;
}

Subrange::Subrange(Expression *b, Expression *h, Expression *l, uint w) : Expression() {
  base = b; high = h; low = l; width = w;
}

bool Subrange::isSubrange() {return true;}

bool Subrange::isInteger() {return true;}

void Subrange::displayNoParens(ostream& os) {
  base->display(os);
  os << "[";
  high->display(os);
  os << ":";
  low->display(os);
  os << "]";
}

Expression *Subrange::subst(SymRef *var, Expression *val) {
  Expression *newBase = base->subst(var, val);
  Expression *newHigh = high->subst(var, val);
  Expression *newLow = low->subst(var, val);
  return (newBase == base && newHigh == high && newLow == low)
           ? this : new Subrange(newBase, newHigh, newLow);
}

char *newstr(const char *str) {
  char *result = new char[strlen(str)+1];
  strcpy(result, str);
  return result;
}

Sexpression *Subrange::ACL2Expr(bool isBV) {
  Sexpression *b = base->ACL2Expr(true);
  Sexpression *hi = high->ACL2Expr();
  Sexpression *lo = low->ACL2Expr();
  return new Plist(&s_bits, b, hi, lo);
}

Sexpression *Subrange::ACL2Assign(Sexpression *rval) {
  Sexpression *b = base->ACL2Expr(true);
  Sexpression *hi = high->ACL2Expr();
  Sexpression *lo = low->ACL2Expr();
  uint n = (((RegType*)(base->exprType()))->width)->evalConst();
  Integer *s = new Integer(n);
  return base->ACL2Assign(new Plist(&s_setbits, b, s, hi, lo, rval));
}

uint Subrange::ACL2ValWidth() {
  if (high->isConst() && low->isConst()) {
    return high->evalConst() - low->evalConst() + 1;
  }
  else if (high->isPlusConst(low)) {
    return high->getPlusConst() + 1;
  }
  else {
    return width;
  }
}

// class PrefixExpr : public Expression
// ------------------------------------

// Data members: Expression *expr; const char *op;


PrefixExpr::PrefixExpr(Expression *e, const char *o) : Expression() {expr = e; op = o;}

bool PrefixExpr::isConst() {return expr->isConst();}

int PrefixExpr::evalConst() {
  int val = expr->evalConst();
  if (!strcmp(op, "+")) {
    return val;
  }
  else if (!strcmp(op, "-")) {
    return -val;
  }
  else if (!strcmp(op, "~")) {
    return -1 - val;
  }
  else if (!strcmp(op, "!")) {
    return val ? 1 : 0;
  }
  else assert(false);
}

bool PrefixExpr::isInteger() {return expr->isInteger();}

void PrefixExpr::displayNoParens(ostream& os) {
  os << op;
  expr->display(os);
}

Expression *PrefixExpr::subst(SymRef *var, Expression *val) {
  Expression *newExpr = expr->subst(var, val);
  return (newExpr == expr) ? this : new PrefixExpr(newExpr, op);
}

Type *PrefixExpr::exprType() {
  if (!strcmp(op, "~")) {
    return expr->exprType();
  }
  else {
    return NULL;
  }
}

Sexpression *PrefixExpr::ACL2Expr(bool isBV) {
  Sexpression *s = expr->ACL2Expr();
  if (!strcmp(op, "+")) {
    return s;
  }
  else if (!strcmp(op, "-")) {
    return new Plist(&s_minus, s);
  }
  else if (!strcmp(op, "!")) {
    return new Plist(&s_lognot1, s);
  }
  else if (!strcmp(op, "~")) {
    Type *t = exprType();
    if (t) {
       Plist *bv = new Plist(&s_lognot, expr->ACL2Expr(true));
       if (isBV && t->isRegType()) {
         uint w = (((RegType*)t)->width)->evalConst();
         return new Plist(&s_bits, bv, new Integer(w - 1), &i_0);
       }
       else {
         return t->ACL2Eval(bv);
         //?? return bv;
       }
    }
    else {
      return new Plist(&s_lognot, s);
    }
  }
  else assert(false);
}

bool PrefixExpr::isEqual(Expression *e) {
  return this == e || e->isEqualPrefix(op, expr);
}

bool PrefixExpr::isEqualPrefix(const char *o, Expression *e) {
  return !strcmp(o, op) && e->isEqual(expr);
}


// class CastExpr : public Expression
// ----------------------------------

// Data members: Expression *expr; Type *type;

CastExpr::CastExpr(Expression *e, Type *t) : Expression() {expr = e; type = t;}

Type* CastExpr::exprType() {return type;}

bool CastExpr::isConst() {return expr->isConst();}

int CastExpr::evalConst() {return expr->evalConst();}

bool CastExpr::isInteger() {return expr->isInteger();}

void CastExpr::displayNoParens(ostream& os) {
  expr->display(os);
}

Expression *CastExpr::subst(SymRef *var, Expression *val) {
  Expression *newExpr = expr->subst(var, val);
  return (newExpr == expr) ? this : new CastExpr(newExpr, type);
}

Sexpression *CastExpr::ACL2Expr(bool isBV) {return expr->ACL2Expr();}


// class BinaryExpr : public Expression
// ------------------------------------

// Data members: Expression *expr1; Expression *expr2; const char *op;

BinaryExpr::BinaryExpr(Expression *e1, Expression *e2, const char *o) : Expression() {
  expr1 = e1; expr2 = e2; op = o;
}

bool BinaryExpr::isConst() {return expr1->isConst() && expr2->isConst();}

int BinaryExpr::evalConst() {
  int val1 = expr1->evalConst();
  int val2 = expr2->evalConst();
  if (!strcmp(op, "+")) return val1 + val2;
  if (!strcmp(op, "-")) return val1 - val2;
  if (!strcmp(op, "*")) return val1 * val2;
  if (!strcmp(op, "/")) return val1 / val2;
  if (!strcmp(op, "%")) return val1 % val2;
  if (!strcmp(op, "<<")) return val1 << val2;
  if (!strcmp(op, ">>")) return val1 >> val2;
  if (!strcmp(op, "&")) return val1 & val2;
  if (!strcmp(op, "^")) return val1 ^ val2;
  if (!strcmp(op, "|")) return val1 | val2;
  if (!strcmp(op, "<")) return val1 < val2;
  if (!strcmp(op, ">")) return val1 > val2;
  if (!strcmp(op, "<=")) return val1 <= val2;
  if (!strcmp(op, ">=")) return val1 >= val2;
  if (!strcmp(op, "==")) return val1 == val2;
  if (!strcmp(op, "!=")) return val1 != val2;
  if (!strcmp(op, "&&")) return val1 && val2;
  if (!strcmp(op, "||")) return val1 || val2;
  assert(false);
}

bool BinaryExpr::isInteger() {return expr1->isInteger() && expr2->isInteger();}

void BinaryExpr::displayNoParens(ostream& os) {
  expr1->display(os);
  os << " " << op << " ";
  expr2->display(os);
}

Expression *BinaryExpr::subst(SymRef *var, Expression *val) {
  Expression *newExpr1 = expr1->subst(var, val);
  Expression *newExpr2 = expr2->subst(var, val);
  return (newExpr1 == expr1 && newExpr2 == expr2) ? this : new BinaryExpr(newExpr1, newExpr2, op);
}

Type *BinaryExpr::exprType() {
  Type *t1 =  expr1->exprType();
  Type *t2 =  expr2->exprType();
  if ((!strcmp(op, "&") || !strcmp(op, "|") || !strcmp(op, "^")) && (t1 == t2)) {
    return t1;
  }
  else {
    return NULL;
  }
}

Sexpression *BinaryExpr::ACL2Expr(bool isBV) {
  Symbol *ptr;
  Sexpression *sexpr1 = expr1->ACL2Expr();
  Sexpression *sexpr2 = expr2->ACL2Expr();
  if (expr1->isFP() && !strcmp(op, "<<")) {
    return new Plist(&s_times, sexpr1, new Plist(&s_expt, &i_2, sexpr2));
  }
  else if (expr1->isFP() && !strcmp(op, ">>")) {
    return new Plist(&s_divide, sexpr1, new Plist(&s_expt, &i_2, sexpr2));
  }
  if (!strcmp(op, "+")) ptr = &s_plus; else
  if (!strcmp(op, "-")) ptr = &s_minus; else
  if (!strcmp(op, "*")) ptr = &s_times; else
  if (!strcmp(op, "/")) ptr = &s_floor; else
  if (!strcmp(op, "%")) ptr = &s_rem; else
  if (!strcmp(op, "<<")) ptr = &s_ash; else
  if (!strcmp(op, ">>")) {ptr = &s_ash; sexpr2 = new Plist(&s_minus, sexpr2);} else
  if (!strcmp(op, "&")) ptr = &s_logand; else
  if (!strcmp(op, "^")) ptr = &s_logxor; else
  if (!strcmp(op, "|")) ptr = &s_logior; else
  if (!strcmp(op, "<")) ptr = &s_logless; else
  if (!strcmp(op, ">")) ptr = &s_loggreater; else
  if (!strcmp(op, "<=")) ptr = &s_logleq; else
  if (!strcmp(op, ">=")) ptr = &s_loggeq; else
  if (!strcmp(op, "==")) ptr = &s_logeq; else
  if (!strcmp(op, "!=")) ptr = &s_logneq; else
  if (!strcmp(op, "&&")) ptr = &s_logand1; else
  if (!strcmp(op, "||")) ptr = &s_logior1; else
  assert(false);
  if (exprType() && (ptr == &s_logand || ptr == &s_logior || ptr == &s_logxor)) {
    Plist *bv = new Plist(ptr, expr1->ACL2Expr(true), expr2->ACL2Expr(true));
    return isBV ? bv : exprType()->ACL2Eval(bv);
  }
  else {
    return new Plist(ptr, sexpr1, sexpr2);
  }
}

bool BinaryExpr::isEqual(Expression *e) {
  return this == e || e->isEqualBinary(op, expr1, expr2);
}

bool BinaryExpr::isEqualBinary(const char *o, Expression *e1, Expression *e2) {
  return !strcmp(o, op) && e1->isEqual(expr1) && e2->isEqual(expr2);
}

bool BinaryExpr::isPlusConst(Expression *e) {
  return !strcmp(op, "+") && expr1->isEqual(e) && expr2->isConst();
}

int BinaryExpr::getPlusConst() {
  return expr2->evalConst();
}


// class CondExpr : public Expression (conditional expression)
// -----------------------------------------------------------

// Data members:  Expression *expr1; Expression *expr2; Expression *test;


CondExpr::CondExpr(Expression *e1, Expression *e2, Expression *t) : Expression() {
  expr1 = e1; expr2 = e2; test = t;
}

bool CondExpr::isInteger() {return expr1->isInteger() && expr2->isInteger();}

void CondExpr::displayNoParens(ostream& os) {
  test->display(os);
  os << " ? ";
  expr1->display(os);
  os << " : ";
  expr2->display(os);
}

Expression *CondExpr::subst(SymRef *var, Expression *val) {
  Expression *newExpr1 = expr1->subst(var, val);
  Expression *newExpr2 = expr2->subst(var, val);
  Expression *newTest = test->subst(var, val);
  return (newExpr1 == expr1 && newExpr2 == expr2 && newTest == test)
           ? this : new CondExpr(newExpr1, newExpr2, newTest);
}

Sexpression *CondExpr::ACL2Expr(bool isBV) {
  return new Plist(&s_if1, test-> ACL2Expr(), expr1->ACL2Expr(), expr2->ACL2Expr());
}


// class MultipleValue : public Expression
// ---------------------------------------

// Data members: MvType *type; Expression *expr[8];

MultipleValue::MultipleValue(MvType *t, Expression **e) : Expression() {
  type = t;
  for (uint i=0; i<8; i++) expr[i] = e[i];
}

MultipleValue::MultipleValue(MvType *t, List<Expression> *e) : Expression() {
  type = t;
  for (uint i=0; i<8; i++) {
    if (e) {
      expr[i] = e->value;
      e = e->pop();
    }
    else {
      expr[i] = NULL;
    }
  }
}

void MultipleValue::displayNoParens(ostream& os) {
  os << "<";
  expr[0]->display(os);
  os << ", ";
  expr[1]->display(os);
  if (expr[2]) {
    os << ", ";
    expr[2]->display(os);
    if (expr[3]) {
      os << ", ";
      expr[3]->display(os);
      if (expr[4]) {
        os << ", ";
        expr[4]->display(os);
        if (expr[5]) {
          os << ", ";
          expr[5]->display(os);
          if (expr[6]) {
            os << ", ";
            expr[6]->display(os);
            if (expr[7]) {
              os << ", ";
              expr[7]->display(os);
	    }
          }
	}
      }
    }
  }
  os << ">";
}

Expression *MultipleValue::subst(SymRef *var, Expression *val) {
  Expression *newExpr[8];
  bool isNew = false;
  for (uint i=0; i<8; i++) {
    newExpr[i] = expr[i] ? expr[i]->subst(var, val) : NULL;
    if (newExpr[i] != expr[i]) {isNew = true;}
  }
  return isNew ? new MultipleValue(type, newExpr) : this;
}

Sexpression *MultipleValue::ACL2Expr(bool isBV) {
  Plist *result = new Plist(&s_mv);
  for (uint i=0; i<8 && expr[i]; i++) {
    result->add(type->type[i]->derefType()->ACL2Assign(expr[i]));
  }
  return result;
}


//***********************************************************************************
// class Statement
//***********************************************************************************

// Derived classes:

//   SimpleStatement       (statement that does not include substatements)
//     VarDec              (variable declaration)
//       ConstDec          (constant declaration)
//     MulVarDec           (multiple variable declaration)
//     MulConstDec         (multiple constant declaration)
//     BreakStmt           (break -- may occur only within a switch)
//     ReturnStmt          (return)
//     Assertion           (assert)
//     Assignment          (=, ++, --, +=, etc.)
//     MultipleAssignment  (assignment of multiple function value)
//     NullStmt            (null statement)
//   Block                 (list of statements)
//   IfStmt                (if or if ... else)
//   ForStmt               (for)
//   SwitchStmt            (switch)

Statement::Statement() {}

// This method is designed to handle if ... else if ... :

void Statement::displayAsRightBranch(ostream& os, uint indent) { // virtual (overridden by IfStmt)
  display(os, indent + 2);
}

// This method is designed to handle nested blocks:

void Statement::displayWithinBlock(ostream& os, uint indent) { // virtual (overridden by Block)
  display(os, indent);
}

// Turn into a block if not already one:

Block *Statement::blockify() { // virtual (overridden by Block)
  return new Block(this);
}

// Create a block consisting of s appended to this:

Block *Statement::blockify(Statement *s) { // virtual (overridden by Block)
  return new Block(this, s);
}

// Substitute expr for each ocurrence of var in statement; var is assumed not to occur in the left
// side of any declaration or assignment:

Statement* Statement::subst(SymRef *var, Expression *expr) { // virtual
  return this;
}

// Translate to an S-expression for ACL2 translation:

Sexpression *Statement::ACL2Expr() { // virtual
  display(cout); cout << endl;
  assert(!"Statement is not intended to be converted to an S-expression");
  return NULL;
}

void Statement::noteReturnType(Type *t) { // virtual (overridden by Block, ReturnStmt, and IfStmt)
}

void Statement::markAssertions(FunDef *f) { // virtual (overridden by Assertion)
}

// class SimpleStatement : public Statement
// ----------------------------------------

SimpleStatement::SimpleStatement() : Statement() {}

void SimpleStatement::display(ostream& os, uint indent) {
  os << "\n";
  if (indent) {os << setw(indent) << " ";}
  displaySimple(os);
  os << ";";
}


// class VarDec : public SimpleStatement, public SymDec (variable declaration)
// ---------------------------------------------------------------------------

VarDec::VarDec(const char *n, Type *t, Expression *i) : SimpleStatement(), SymDec(n, t, i) {}

void VarDec::displaySimple(ostream& os) {displaySymDec(os);}

Statement* VarDec::subst(SymRef *var, Expression *val) {
  assert(var->symDec != this);
  if (init) {
    Expression *newInit = init->subst(var, val);
    return (init == newInit) ? this : new VarDec(getname(), type, newInit);
  }
  else {
    return this;
  }
}

Sexpression *VarDec::ACL2Expr() {
  Sexpression *val;
  if (type->derefType()->isArrayType()) {
    if (!init) {
      val = new Plist();
    }
    else if (isROM()) {
      val = new Plist(&s_quote, init->ACL2Expr());
    }
    else {
      val = init->ACL2ArrayExpr();
    }
  }
  else if (init) {
    val = type->derefType()->ACL2Assign(init);
  }
  else if (type->derefType()->isStructType()) {
    val = new Plist();
  }
  else {
    val = &i_0;
  }
  return new Plist(&s_declare, sym, val);
}

Sexpression *VarDec::ACL2SymExpr() {
  return sym;
}

// class ConstDec : public VarDec
// ------------------------------

ConstDec::ConstDec(const char *n, Type *t, Expression *i) : VarDec(n, t, i) {}

void ConstDec::displaySimple(ostream& os) {
  os << "const ";
  VarDec::displaySimple(os);
}

bool ConstDec::isConst() {return type->isIntegerType();}

Statement *ConstDec::subst(SymRef *var, Expression *val) {return this;}

bool ConstDec::isGlobal() {
  List<ConstDec> *decs = prog.constDecs;
  while (decs) {
    if (decs->value == this) return true;
    decs = decs->next;
  }
  return false;
}

bool ConstDec::isROM() {
  return isGlobal() && type->isArrayType() && !type->isArrayParamType();
}

Sexpression *ConstDec::ACL2SymExpr() {
  if (isGlobal()) {
    return new Plist(sym);
  }
  else {
    return sym;
  }
}

// class MulVarDec : public SimpleStatement  (multiple variable declaration)
// ---------------------------------------------------------------------------

MulVarDec::MulVarDec(VarDec *dec1, VarDec *dec2) : SimpleStatement() {
  decs = new List<VarDec>(dec1, dec2);
}

MulVarDec::MulVarDec(List<VarDec> *d) : SimpleStatement() {
  decs = d;
}

Statement *MulVarDec::subst(SymRef *var, Expression *val) {
  List<VarDec> *newDecs = new List<VarDec>((VarDec*)(decs->value->subst(var, val)));
  List<VarDec> *d = decs->next;
  while (d) {
    newDecs->add((VarDec*)(d->value->subst(var, val)));
    d = d->next;
  }
  return new MulVarDec(newDecs);
}

Sexpression *MulVarDec::ACL2Expr() {
  Plist *result = new Plist(&s_list);
  List<VarDec> *ptr = decs;
  while (ptr) {
    result->add(ptr->value->ACL2Expr());
    ptr = ptr->next;
  }
  return result;
}

void MulVarDec::displaySimple(ostream& os) {
  List<VarDec> *dlist = decs;
  VarDec *d = decs->value;
  d->type->displayVarType(os);
  while (dlist) {
    os << " ";
    d->type->displayVarName(d->getname(), os);
    if (d->init) {
      os << " = ";
      d->init->display(os);
    }
    dlist = dlist->next;
    if (dlist) {
      d = dlist->value;
      os << ",";
    }
  }
}

// class MulConstDec : public SimpleStatement  (multiple constant declaration)
// ---------------------------------------------------------------------------

MulConstDec::MulConstDec(ConstDec *dec1, ConstDec *dec2) : SimpleStatement() {
  decs = new List<ConstDec>(dec1, dec2);
}

MulConstDec::MulConstDec(List<ConstDec> *d) : SimpleStatement() {
  decs = d;
}

Statement *MulConstDec::subst(SymRef *var, Expression *val) {
  List<ConstDec> *newDecs = new List<ConstDec>((ConstDec*)(decs->value->subst(var, val)));
  List<ConstDec> *d = decs->next;
  while (d) {
    newDecs->add((ConstDec*)(d->value->subst(var, val)));
    d = d->next;
  }
  return new MulConstDec(newDecs);
}

Sexpression *MulConstDec::ACL2Expr() {
  Plist *result = new Plist(&s_list);
  List<ConstDec> *ptr = decs;
  while (ptr) {
    result->add(ptr->value->ACL2Expr());
    ptr = ptr->next;
  }
  return result;
}

void MulConstDec::displaySimple(ostream& os) {
  List<ConstDec> *dlist = decs;
  ConstDec *d = decs->value;
  d->type->displayVarType(os);
  while (dlist) {
    os << " ";
    d->type->displayVarName(d->getname(), os);
    if (d->init) {
      os << " = ";
      d->init->display(os);
    }
    dlist = dlist->next;
    if (dlist) {
      d = dlist->value;
      os << ",";
    }
  }
}

// class TempParamDec : public VarDec  (template parameter declaration)
// --------------------------------------------------------------------

TempParamDec::TempParamDec(const char *n, Type *t) : SymDec(n, t) {init = &i_1;}

bool TempParamDec::isConst() {return true;}

Sexpression *TempParamDec::ACL2SymExpr() {
  return init ? type->derefType()->ACL2Assign(init) : &i_0;
}


// class BreakStmt : public SimpleStatement
// ----------------------------------------

BreakStmt::BreakStmt() : SimpleStatement() {}

void BreakStmt::displaySimple(ostream& os) {
  os << "break";
}

Sexpression *BreakStmt::ACL2Expr() {
  return &s_break;
}

BreakStmt breakStmt;


// class ReturnStmt : public SimpleStatement
// -----------------------------------------

// Data members: Expression *value;

ReturnStmt::ReturnStmt(Expression *v) : SimpleStatement() {value = v;}

void ReturnStmt::displaySimple(ostream& os) {
  os << "return ";
  value->display(os);
}

Statement *ReturnStmt::subst(SymRef *var, Expression *val) {
  Expression *newValue = value->subst(var, val);
  return (value == newValue) ? this : new ReturnStmt(newValue);
}

Sexpression *ReturnStmt::ACL2Expr() {
  return new Plist(&s_return, returnType->derefType()->ACL2Assign(value));
}

void ReturnStmt::noteReturnType(Type *t) {
  returnType = t;
}


// class Assertion : public SimpleStatement
// ----------------------------------------

// Data member: Expression *expr;

Assertion::Assertion(Expression *e) : SimpleStatement() {expr = e;}

void Assertion::displaySimple(ostream& os) {
  os << "assert(";
  expr->display(os);
  os << ")";
}

Statement *Assertion::subst(SymRef *var, Expression *val) {
  Expression *newExpr = expr->subst(var, val);
  return (expr == newExpr) ? this : new Assertion(newExpr);
}

Sexpression *Assertion::ACL2Expr() {
  return new Plist(&s_assert, expr->ACL2Expr(), new Symbol(funDef->getname()));
}

void Assertion::markAssertions(FunDef *f) {
  funDef = f;
}
// class Assignment : public SimpleStatement
// -----------------------------------------

// Data members: Expression *lval; const char* op; Expression *rval;

Assignment::Assignment(Expression *l, const char *o, Expression *r) : SimpleStatement() {
  lval = l; op = o; rval = r;
}

void Assignment::displaySimple(ostream& os) {
  lval->display(os);
  if (rval) {
    os << " " << op << " ";
    rval->display(os);
  }
 else {
   os << op;
  }
}

Statement *Assignment::subst(SymRef *var, Expression *val) {
  Expression *newL = lval->subst(var, val);
  Expression *newR = rval ? rval->subst(var, val) : NULL;
  return (lval == newL) && (rval == newR) ? this : new Assignment(newL, op, newR);
}

Sexpression *Assignment::ACL2Expr() {
  Expression *expr = rval;
  if (!strcmp(op, "=")) {
    expr = rval;
  }
  else if (!strcmp(op, "++")) {
    expr = new BinaryExpr(lval, &i_1, "+");
  }
  else if (!strcmp(op, "--")) {
    expr = new BinaryExpr(lval, &i_1, "-");
  }
  else if (!strcmp(op, ">>=")) {
    expr = new BinaryExpr(lval, rval, ">>");
  }
  else if (!strcmp(op, "<<=")) {
    expr = new BinaryExpr(lval, rval, "<<");
  }
  else if (!strcmp(op, "+=")) {
    expr = new BinaryExpr(lval, rval, "+");
  }
  else if (!strcmp(op, "-=")) {
    expr = new BinaryExpr(lval, rval, "-");
  }
  else if (!strcmp(op, "*=")) {
    expr = new BinaryExpr(lval, rval, "*");
  }
  else if (!strcmp(op, "%=")) {
    expr = new BinaryExpr(lval, rval, "%");
  }
  else if (!strcmp(op, "&=")) {
    expr = new BinaryExpr(lval, rval, "&");
  }
  else if (!strcmp(op, "^=")) {
    expr = new BinaryExpr(lval, rval, "^");
  }
  else if (!strcmp(op, "|=")) {
    expr = new BinaryExpr(lval, rval, "|");
  }
  else {
    assert(!"Unknown assignment operator");
  }
  Type *t = lval->exprType();
  Sexpression *sexpr = t ? t->ACL2Assign(expr) : expr->ACL2Expr();
  return lval->ACL2Assign(sexpr);
}

// class AssignBit : public SimpleStatement (bit assignment)
// ---------------------------------------------------------

// Data members: Expression *base; Expression *index; Expression *val;

AssignBit::AssignBit(Expression *b, Expression *i, Expression *v) : SimpleStatement() {
  base = b, index = i; val = v;
}

void AssignBit::displaySimple(ostream& os) {
  base->display(os);
  os << ".assign_bit(";
  index->display(os);
  os << ", ";
  val->display(os);
  os << ")";
}

// class AssignRange : public SimpleStatement (subrange assignment)
// -----------------------------------------------------------------

// Data members: Expression *base; Expression *high; Expression *low; Expression *width; Expression *val;

AssignRange::AssignRange(Expression *b, Expression *h, Expression *l, Expression *w, Expression *v)
 : SimpleStatement() {base = b, high = h; low = l; width = w; val = v;}

void AssignRange::displaySimple(ostream& os) {
  base->display(os);
  os << ".assign_range<";
  high->display(os);
  os << ", ";
  low->display(os);
  if (width) {
    os << ", ";
    width->display(os);
  }
  os << ">(";
  val->displayNoParens(os);
  os << ")";
}

// class MultipleAssignment : public SimpleStatement
// -------------------------------------------------

// Data members: Expression *lval[8]; FunCall *rval;

MultipleAssignment::MultipleAssignment(FunCall *r, List<Expression> *e) : SimpleStatement() {
  for (uint i=0; i<8; i++) {
    if (e) {
      lval[i] = e->value;
      e = e->pop();
    }
    else {
      lval[i] = NULL;
    }
  }
  rval = r;
}

void MultipleAssignment::displaySimple(ostream& os) {
  os << "<";
  lval[0]->display(os);
  for (uint i=1; i<8 && lval[i]; i++) {
    os << ", ";
    lval[i]->display(os);
  }
  os << "> = ";
  rval->display(os);
}

Statement *MultipleAssignment::subst(SymRef *var, Expression *val) {
  Expression *newR = rval->subst(var, val);
  bool changed = (newR != rval);
  List<Expression> *newL;
  for (uint i=0; i<8 && lval[i]; i++) {
    Expression *temp = lval[i]->subst(var, val);
    if (temp != lval[i]) changed = true;
    if (i == 0) {
      newL = new List<Expression>(temp);
    }
    else {
      newL->add(temp);
    }
  }
  return changed ? new MultipleAssignment((FunCall*)newR, newL) : this;
}

// In the event that each target of a multiple assignment is a simple variable,
// the corrersponding S-expression  has the form

//   (MV-ASSIGN (var1 ... vark) fncall).

// Otherwise, for each target that is not a simple variable (i.e., a reference to an array
// entry, a struct field, a subrange, or a bit), a temporary variable and an additional
// assignment are introduced, and the S-expression has the form

//   (BLOCK (MV-ASSIGN (var1 ... vark) fncall) (ASSIGN ...) ... (ASSIGN ...)).

// For example, the statement

//   foo(...).assign(x, y[i], z.range(j, k))

// where y is an array and z is a register of width 8, generates the following:

//   (BLOCK (MV-ASSIGN (X TEMP-0 TEMP-1) (FOO ...))
//          (ASSIGN Y (AS I TEMP-0 Y))
//          (ASSIGN Z (SETBITS Z 8 J K TEMP-1))).

Sexpression *MultipleAssignment::ACL2Expr() {
  Plist *vars = new Plist();
  Plist *result = new Plist(&s_mv_assign, vars, rval->ACL2Expr());
  bool isBlock = false;
  for (uint i=0; i<8 && lval[i]; i++) {
    if (lval[i]->isSymRef()) {
      vars->add(((SymRef*)lval[i])->symDec->sym);
    }
    else {
      if (!isBlock) {
        result = new Plist(result);
        isBlock = true;
      }
      vars->add(&s_temp[i]);
      result->add(lval[i]->ACL2Assign(&s_temp[i]));
      result->push(new Plist(&s_declare, &s_temp[i]));
    }
  }
  if (isBlock) {
    result->push(&s_block);
  }
  return result;
}

// class NullStmt : public SimpleStatement (null statement)
// --------------------------------------------------

NullStmt::NullStmt() : SimpleStatement() {}

void NullStmt::displaySimple(ostream& os) {}

Sexpression *NullStmt::ACL2Expr() {
  return new Plist(&s_null);
}

NullStmt nullStmt;


// class Block : public Statement
// ------------------------------

// Data member: List<Statement> *stmtList;

Block::Block(List<Statement> *s) : Statement() {stmtList = s;}

Block::Block(Statement* s): Statement() {stmtList = new List<Statement>(s);}

Block::Block(Statement* s1, Statement* s2): Statement() {
    stmtList = new List<Statement>(s1, new List<Statement>(s2));
}

Block::Block(Statement* s1, Statement* s2, Statement* s3): Statement() {
  stmtList = new List<Statement>(s1, new List<Statement>(s2, new List<Statement>(s3)));
}

Block *Block::blockify() {return this;}

Block *Block::blockify(Statement *s) {
  return new Block(stmtList ? stmtList->copy()->add(s) : new List<Statement>(s));
}

void Block::display(ostream& os, uint indent) {
  os << " {";
  if (stmtList) {
    List<Statement> *ptr = stmtList;
    while (ptr) {
      ptr->value->displayWithinBlock(os, indent);
      ptr = ptr->next;
    }
    os << "\n";
    if (indent > 2) {os << setw(indent - 2) << " ";}
  }
  os << "}";
}

void Block::displayWithinBlock(ostream& os, uint indent) {
  os << "\n" << setw(indent) << (indent ? " " : "") << "{";
  List<Statement> *ptr = stmtList;
  while (ptr) {
    ptr->value->displayWithinBlock(os, indent+2);
    ptr = ptr->next;
  }
  os << "\n";
  if (indent) {os << setw(indent) << " ";}
  os << "}";
}

Statement *Block::subst(SymRef *var, Expression *val) {
  List<Statement> *newList = NULL;
  bool changed = false;
  for (int i=stmtList->length()-1; i>=0; i--) {
    List<Statement> *subList = stmtList->nthl(i);
    Statement *s = subList->value;
    Statement *sNew = s->subst(var, val);
    if (sNew != s) {
      changed = true;
    }
    if (changed) {
      newList = new List<Statement>(sNew, newList);
    }
    else {
      newList = subList;
    }
  }
  return changed ? new Block(newList) : this;
}

Sexpression *Block::ACL2Expr() {
  Plist *result = new Plist(&s_block);
  List<Statement> *ptr = stmtList;
  while (ptr) {
    result->add(ptr->value->ACL2Expr());
    ptr = ptr->next;
  }
  return result;
}

void Block::noteReturnType(Type *t) {
  List<Statement> *ptr = stmtList;
  while (ptr) {
    ptr->value->noteReturnType(t);
    ptr = ptr->next;
  }
}

void Block::markAssertions(FunDef *f) {
  List<Statement> *ptr = stmtList;
  while (ptr) {
    ptr->value->markAssertions(f);
    ptr = ptr->next;
  }
}

// class IfStmt : public Statement
// -------------------------------

// Data members: Expression *test; Statement *left; Statement *right;

IfStmt::IfStmt(Expression *t, Statement *l, Statement *r) : Statement() {
  test = t;
  left = l;
  right = r;
}

void IfStmt::display(ostream& os, uint indent) {
  os << "\n" << setw(indent) << " ";
  displayAsRightBranch(os, indent);
}

void IfStmt::displayAsRightBranch(ostream& os, uint indent) {
  os << "if (";
  test->display(os);
  os << ")";
  left->display(os, indent+2);
  if (right) {
    os << "\n" << setw(indent) << " " << "else ";
    right->displayAsRightBranch(os, indent);
  }
}

Statement *IfStmt::subst(SymRef *var, Expression *val) {
  Expression *t = test->subst(var, val);
  Statement *l = left->subst(var, val);
  Statement *r = right ? right->subst(var, val) : NULL;
  return (t == test && l == left && r == right) ? this : new IfStmt(t, l, r);
}

Sexpression *IfStmt::ACL2Expr() {
  return new Plist(&s_if, test->ACL2Expr(), left->blockify()->ACL2Expr(), right ? right->blockify()->ACL2Expr() : new Plist());
}

void IfStmt::noteReturnType(Type *t) {
  left->noteReturnType(t);
  if (right) right->noteReturnType(t);
}

void IfStmt::markAssertions(FunDef *f) {
  left->markAssertions(f);
  if (right) right->markAssertions(f);
}

// class ForStmt : public Statement
// --------------------------------

// Data members: SimpleStatement *init; Expression *test; Assignment *update; Statement *body;

ForStmt::ForStmt(SimpleStatement *v, Expression *t, Assignment *u, Statement *b) : Statement() {
  init = v;
  test = t;
  update = u;
  body = b;
}

void ForStmt::display(ostream& os, uint indent) {
  os << "\n" << setw(indent) << " " << "for (";
  init->displaySimple(os);
  os << "; ";
  test->display(os);
  os << "; ";
  update->displaySimple(os);
  os << ")";
  body->display(os, indent+2);
}

Statement *ForStmt::subst(SymRef *var, Expression *val) {
  SimpleStatement *v = (SimpleStatement*)init->subst(var, val);
  Expression *t = test->subst(var, val);
  Assignment *u = (Assignment*)update->subst(var, val);
  Statement *b = body->subst(var, val);
  return (v == init && t == test && u == update && b == body) ? this : new ForStmt(v, t, u, b);
}

Sexpression *ForStmt::ACL2Expr() {
  Sexpression *sinit = init->ACL2Expr();
  Sexpression *stest = test->ACL2Expr();
  Sexpression *supdate = ((Plist*)(update->ACL2Expr()))->list->nth(2);
  return new Plist(&s_for, new Plist(sinit, stest, supdate), body->blockify()->ACL2Expr());
}

void ForStmt::markAssertions(FunDef *f) {
  body->markAssertions(f);
}

// class Case : public Statement (component of switch statement)
// -------------------------------------------------------------

// Data members:   Expression *label; List<Statement> *action;

Case::Case(Expression *l, List<Statement> *a) {label = l; action = a;}

void Case::display(ostream& os, uint indent) {
  os << "\n" << setw(indent) << " ";
  if (label) {
    os << "case ";
    label->display(os);
  }
  else {
    os << "default";
  }
  os << ":";
  List<Statement> *ptr = action;
  while (ptr) {
    ptr->value->displayWithinBlock(os, indent+2);
    ptr = ptr->next;
  }
}

Case* Case::subst(SymRef *var, Expression *val) {
  List<Statement> *newAction = NULL;
  bool changed = false;
  for (int i=action->length()-1; i>=0; i--) {
    List<Statement> *subList = action->nthl(i);
    Statement *s = subList->value;
    Statement *sNew = s->subst(var, val);
    if (sNew != s) {
      changed = true;
    }
    if (changed) {
      newAction = new List<Statement>(sNew, newAction);
    }
    else {
      newAction = subList;
    }
  }
  return changed ? new Case(label, newAction) : this;
}

void Case::markAssertions(FunDef *f) {
  List<Statement> *a = action;
  while (a) {
    a->value->markAssertions(f);
    a = a->next;
  }
}


// class SwitchStmt : public Statement
// -----------------------------------

// Data members: Expression *test; List<Case> *cases;

SwitchStmt::SwitchStmt(Expression *t, List<Case> *c) : Statement() {
  test = t;
  cases = c;
}

void SwitchStmt::display(ostream& os, uint indent) {
  os << "\n" << setw(indent) << " " << "switch (";
  test->display(os);
  os << ") {";
  cases->displayList(os, indent);
  os << "\n" << setw(indent) << " " << "}";
}

Statement* SwitchStmt::subst(SymRef *var, Expression *val) {
  List<Case> *newCases = NULL;
  bool changed = false;
  for (int i=cases->length()-1; i>=0; i--) {
    List<Case> *subList = cases->nthl(i);
    Case *c = subList->value;
    Case *cNew = c->subst(var, val);
    if (cNew != c) {
      changed = true;
    }
    if (changed) {
      newCases = new List<Case>(cNew, newCases);
    }
    else {
      newCases = subList;
    }
  }
  return changed ? new SwitchStmt(test, newCases) : this;
}

Sexpression *SwitchStmt::ACL2Expr() {
  List<Sexpression> *result = new List<Sexpression>(&s_switch, test->ACL2Expr());
  List<Case> *clist = cases;
  List<Sexpression> *labels = NULL;
  Case *c;
  Expression *l;
  List<Statement> *a;
  List<Sexpression> *s;
  while (clist) {
    Case *c = clist->value;
    l = c->label;
    l = c->label;
    a = c->action;
    a = c->action;
    if (l) {
      labels = labels ? labels->add(l->ACL2Expr()) : new List<Sexpression>(l->ACL2Expr());
    }
    if (a) {
      Sexpression *slabel = !labels ? &s_t : !(labels->next) ? labels->value : new Plist(labels);
      s = new List<Sexpression>(slabel);
      while (a && a->value != &breakStmt) {
        s->add(a->value->ACL2Expr());
        a = a->next;
      }
      result->add(new Plist(s));
      labels = NULL;
    }
    clist = clist->next;
  }
  if (l) result->add(new Plist(&s_t));
  return new Plist(result);
}

void SwitchStmt::markAssertions(FunDef *f) {
  List<Case> *c = cases;
  while (c) {
    c->value->markAssertions(f);
    c = c->next;
  }
}


//***********************************************************************************
// class FunDef
//***********************************************************************************

// Data members: Symbol *sym; Type *returnType; List<VarDec> *params; Block *body;

FunDef::FunDef(const char *n, Type *t, List<VarDec> *p, Block *b) {
  sym = new Symbol(n);
  returnType = t;
  params = p;
  body = b;
}

uint FunDef::arity() {return params->length();}

char *FunDef::getname() {return sym->name;}

void FunDef::displayDec(ostream& os, uint indent) {
  os << "\n";
  if (indent) {os << setw(indent) << " ";}
  returnType->display(os);
  os << " " << getname() << "(";
  List<VarDec> *ptr = params;
  while (ptr) {
    ptr->value->displaySimple(os);
    ptr = ptr->next;
    if (ptr) {
      os << ", ";
    }
  }
  os << ");";
}

void FunDef::display(ostream& os, const char *prefix, uint indent) {
  os << "\n";
  if (indent) {os << setw(indent) << " ";}
  returnType->display(os);
  os << " " << prefix << getname() << "(";
  List<VarDec> *ptr = params;
  while (ptr) {
    ptr->value->displaySimple(os);
    ptr = ptr->next;
    if (ptr) {
      os << ", ";
    }
  }
  os << ")";
  body->display(os, indent + 2);
  os << "\n";
}

void FunDef::displayACL2Expr(ostream& os) {
  Plist *sparams = new Plist();
  List<VarDec> *ptr = params;
  while (ptr) {
    sparams->add(ptr->value->sym);
    ptr = ptr->next;
  }
  body->noteReturnType(returnType);
  body->markAssertions(this);
  (new Plist(&s_funcdef, sym, sparams, body->blockify()->ACL2Expr()))->display(os);
}


// class Builtin : public FunDef
// -----------------------------

Builtin::Builtin(const char *n, Type *t, Type *a0, Type *a1, Type *a2) : FunDef(n, t, NULL, NULL) {
      if (a0) params = new List<VarDec>(new VarDec("", a0)); else return;
      if (a1) params->add(new VarDec("", a1)); else return;
      if (a2) params->add(new VarDec("", a2));
}


// class Template : public FunDef
// -----------------------------

// Data members: List<TempParamDec> *tempParams; List<TempCall> *calls;

Template::Template(const char *n, Type *t, List<VarDec> *p, Block *b, List<TempParamDec> *tp)
  : FunDef(n, t, p, b) {tempParams = tp;}

void Template::display(ostream& os, const char *prefix, uint indent) {
  os << "\n";
  if (indent) {os << setw(indent) << " ";}
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
  }
  else {
    calls = new List<TempCall>(c);
  }
}

// This is called by both Template::displayACL2Expr and TempCall::ACL2Expr:

void Template::bindParams(List<Expression> *actuals) {
  List<TempParamDec> *formals = tempParams;
  while (formals) {
    assert(actuals);
    formals->value->init = actuals->value,
    formals = formals->next;
    actuals = actuals->next;
  }
}

void Template::displayACL2Expr(ostream& os) {
  List<TempCall> * c = calls;
  uint numCalls = 0;
  Symbol *saveSym = sym;
  while (c) {
    ostringstream ostr;
    ostr << saveSym->name << "-" << numCalls++;
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

//***********************************************************************************
// class Program
//***********************************************************************************

// A program consists of type definitions, global constant declarations, and function definitions.

// Data members: List<DefinedType> *typeDefs; List<ConstDec> *constDecs; List<Template> *templates; List<FunDef> *funDefs;

Program::Program() {
  typeDefs = NULL;
  constDecs = NULL;
  funDefs = NULL;
  templates = NULL;
}

// A program may be displayed in either of two modes:
//   rac: Pseudocode representation.
//   acl2: S-expression representation, to be processed by the ACL2 translator.

void Program::displayTypeDefs(ostream& os, DispMode mode) {
  // Note that type definitions are used in generating S-expressions for constant declarations
  // and function definitions, but are not represented explicitly in the ACL2 translation.
  List<DefinedType> *ptr = typeDefs;
  while (ptr) {
    switch (mode) {
    case rac:
      ptr->value->displayDef(os);
      break;
    case acl2:
      break;
    }
    ptr = ptr->next;
  }
}

void Program::displayConstDecs(ostream& os, DispMode mode) {
  List<ConstDec> *ptr = constDecs;
  while (ptr) {
    switch (mode) {
    case rac:
      ptr->value->display(os);
      break;
    case acl2:
      ptr->value->ACL2Expr()->display(os);
    }
    ptr = ptr->next;
  }
}

void Program::displayFunDefs(ostream& os, DispMode mode, const char *prefix) {
  List<FunDef> *ptr = funDefs;
  while (ptr) {
    FunDef *def =  ptr->value;
    switch (mode) {
    case rac:
      def->display(os);
      break;
    case acl2:
      def->displayACL2Expr(os);
      break;
    }
    ptr = ptr->next;
  }
  os << endl;
}

void Program::displayFunDecs(ostream& os) {
  List<FunDef> *ptr = funDefs;
  while (ptr) {
    ptr->value->displayDec(os);
    ptr = ptr->next;
  }
}

void Program::display(ostream& os, DispMode mode) {
  displayTypeDefs(os, mode);
  os << "\n";
  displayConstDecs(os, mode);
  os << "\n";
  displayFunDefs(os, mode);
}
