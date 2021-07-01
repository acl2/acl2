%{
#include <alloca.h>
#include <cstdlib>
int yylex();
#include "parser.h"
void yyerror(const char *);
extern int yylineno;
extern char yyfilenm[];
extern BreakStmt breakStmt;

Program prog;
List<Builtin> *builtins = new List<Builtin>(new Builtin("abs", &intType, &intType));
Stack<SymDec> *symTab = new Stack<SymDec>;

%}

%union {
  int i;
  char *s;
  Type *t;
  DefinedType *dt;
  Expression *exp;
  FunDef *fd;
  List<Expression> *expl;
  BigList<Expression> *initl;
  StructField *sf;
  List<StructField> *sfl;
  EnumConstDec *ecd;
  List<EnumConstDec> *ecdl;
  VarDec *vd;
  List<VarDec> *vdl;
  TempParamDec *tpd;
  List<TempParamDec> *tdl;
  Statement *stm;
  List<Statement> *stml;
  Case *c;
  List<Case> *cl;
}

%token TYPEDEF CONST STRUCT ENUM TEMPLATE
%token RAC
%token INT UINT INT64 UINT64 BOOL
%token SLC SET_SLC
%token FOR IF ELSE WHILE DO SWITCH CASE DEFAULT BREAK RETURN ASSERT
%token ARRAY TUPLE TIE
%token AC_INT AC_FIXED
%token <s> RSHFT_ASSIGN LSHFT_ASSIGN ADD_ASSIGN SUB_ASSIGN MUL_ASSIGN MOD_ASSIGN
%token <s> AND_ASSIGN XOR_ASSIGN OR_ASSIGN
%token <s> INC_OP DEC_OP
%token <s> RSHFT_OP LSHFT_OP AND_OP OR_OP LE_OP GE_OP EQ_OP NE_OP
%token <s> ID NAT TRUE FALSE TYPEID TEMPLATEID
%token <s> '=' '+' '-' '&' '|' '!' '~' '*' '%' '<' '>' '^' '/'
%start program

%type <t> type_spec typedef_type
%type <t> primitive_type array_param_type mv_type register_type struct_type enum_type
%type <dt>  type_dec typedef_dec
%type <sf> struct_field
%type <sfl> struct_field_list
%type <ecd> enum_const_dec
%type <ecdl> enum_const_dec_list
%type <exp> expression constant integer boolean symbol_ref funcall
%type <exp> array_or_bit_ref subrange array_init case_label
%type <exp> primary_expression postfix_expression prefix_expression mult_expression add_expression
%type <exp> arithmetic_expression rel_expression eq_expression and_expression xor_expression ior_expression
%type <exp> log_and_expression log_or_expression cond_expression
%type <exp> mv_expression struct_ref
%type <fd> func_def func_template
%type <expl> expr_list nontrivial_expr_list arith_expr_list nontrivial_arith_expr_list
%type <initl> array_init_list
%type <vdl> param_dec_list nontrivial_param_dec_list
%type <tpd> template_param_dec
%type <tdl> template_param_dec_list nontrivial_template_param_dec_list
%type <stml> statement_list r_statement_list
%type <stm> statement r_statement block r_block var_dec const_dec untyped_var_dec untyped_const_dec
%type <stm> for_statement for_init multiple_var_dec multiple_const_dec null_statement final_statement
%type <stm> if_statement switch_statement break_statement
%type <stm> simple_statement assignment multiple_assignment assertion return_statement
%type <c> case
%type <cl> case_list
%type <s> assign_op inc_op unary_op

%expect 3

%%

//*************************************************************************************
// Program Structure
//*************************************************************************************

// A program consists of a sequence of type definitions, global constant declarations,
// and function definitions.  The parser produces four linked lists corresponding to
// these sequences, stored as the values of the variables typeDefs, constDecs, and funDefs.

program
  : program program_element {}
  | program_element
  ;

program_element
  : type_dec ';'
    {
      if (!prog.typeDefs) {
        prog.typeDefs = new List<DefinedType>($1);
      }
      else if (prog.typeDefs->find($1->name)) {
        yyerror("Duplicate type definition");
      }
      else {
        prog.typeDefs->add($1);
      }
    }
  | const_dec ';'
    {
      if (!prog.constDecs) {
        prog.constDecs = new List<ConstDec>((ConstDec*)$1);
      }
      else if (prog.constDecs->find(((ConstDec*)$1)->sym->name)) {
        yyerror("Duplicate global constant declaration");
      }
      else {
        prog.constDecs->add((ConstDec*)$1);
      }
    }
  | func_def
    {
      if (!prog.funDefs) {
        prog.funDefs = new List<FunDef>($1);
      }
      else if (prog.funDefs->find($1->sym->name)) {
        yyerror("Duplicate function definition");
      }
      else {
        prog.funDefs->add($1);
      }
    }
  ;

//*************************************************************************************
// Types
//*************************************************************************************

type_dec
  : typedef_dec
  | STRUCT ID struct_type  {$$ = new DefinedType($2, $3);}
  | ENUM ID enum_type      {$$ = new DefinedType($2, $3);}
  ;

typedef_dec
  : TYPEDEF typedef_type ID  {$$ = new DefinedType($3, $2);}
  | typedef_dec '[' arithmetic_expression ']'
    {
      if ($3->isConst() && $3->evalConst() > 0) {
        $1->def = new ArrayType($3, $1->def); $$ = $1;
      }
      else {
        yyerror("Array dimension not a positive integer constant");
      }
    }
  ;

typedef_type
  : primitive_type                           // name of a primitive C numerical type
  | register_type                            // Algorithmic C register class
  | array_param_type                         // instantiation of array class template
  | mv_type                                  // instantiation of mv class template
  | TYPEID  {$$ = prog.typeDefs->find($1);}  // name of a previously declared type
  ;

type_spec
  : typedef_type                           // type that can appear in a typedef declaration
  | STRUCT struct_type  {$$ = $2;}         // standard C structure type
  | ENUM enum_type      {$$ = $2;}         // standard C enumeration type
  ;

primitive_type
  : INT   {$$ = &intType;}
  | UINT  {$$ = &uintType;}
  | INT64   {$$ = &int64Type;}
  | UINT64  {$$ = &uint64Type;}
  | BOOL  {$$ = &boolType;}
  ;

register_type
  : AC_FIXED '<' arithmetic_expression ',' arithmetic_expression ',' TRUE '>'
    {
      if ($3->isConst() && $3->isInteger() && ($3->evalConst() >= 0) & $5->isConst() && $5->isInteger()) {
       $$ = new FixedType($3, $5);
      }
      else {
        yyerror("Illegal parameter of ac_fixed");
      }
    }
  | AC_FIXED '<' arithmetic_expression ',' arithmetic_expression ',' FALSE '>'
    {
      if ($3->isConst() && $3->isInteger() && ($3->evalConst() >= 0) & $5->isConst() && $5->isInteger()) {
       $$ = new UfixedType($3, $5);
      }
      else {
        yyerror("Illegal parameter of ac_fixed");
      }
    }
  | AC_INT '<' arithmetic_expression ',' FALSE '>'
    {
      if ($3->isConst() && $3->isInteger() && $3->evalConst() >= 0) {
       $$ = new UintType($3);
      }
      else {
        yyerror("Illegal parameter of ac_int");
      }
    }
  | AC_INT '<' arithmetic_expression ',' TRUE '>'
    {
      if ($3->isConst() && $3->isInteger() && $3->evalConst() >= 0) {
       $$ = new IntType($3);
      }
      else {
        yyerror("Illegal parameter of ac_int");
      }
    }

  ;

array_param_type
  : ARRAY '<' type_spec ',' arithmetic_expression '>'
    {
      if ($5->isConst() && $5->evalConst() > 0) {
        $$ = new ArrayType($5, $3);
      }
      else {
        yyerror("Non-constant array dimension");
      }
    }
  ;

struct_type
  : '{' struct_field_list '}' {$$ = new StructType($2);}
  ;

struct_field_list
  : struct_field                    {$$ = new List<StructField>($1);}
  | struct_field_list struct_field  {$$ = $1->add($2);}
  ;

struct_field
  : type_spec ID ';'  {$$ = new StructField($1, $2);}
  ;

enum_type
  : '{' enum_const_dec_list '}'  {$$ = new EnumType($2);}
  ;

enum_const_dec_list
  : enum_const_dec                          {$$ = new List<EnumConstDec>($1);}
  | enum_const_dec_list ',' enum_const_dec  {$$ = $1->add($3);}
  ;

enum_const_dec
  : ID                 {$$ = new EnumConstDec($1); symTab->push($$);}
  | ID '=' expression  {$$ = new EnumConstDec($1, $3); symTab->push($$);}
  ;

mv_type
  : TUPLE '<' type_spec ',' type_spec '>'                              {$$ = new MvType(2, $3, $5);}
  | TUPLE '<' type_spec ',' type_spec ',' type_spec '>'                {$$ = new MvType(3, $3, $5, $7);}
  | TUPLE '<' type_spec ',' type_spec ',' type_spec ',' type_spec '>'  {$$ = new MvType(4, $3, $5, $7, $9);}
  | TUPLE '<' type_spec ',' type_spec ',' type_spec ',' type_spec ',' type_spec '>'  {$$ = new MvType(4, $3, $5, $7, $9, $11);}
  | TUPLE '<' type_spec ',' type_spec ',' type_spec ',' type_spec ',' type_spec  ',' type_spec '>'  {$$ = new MvType(4, $3, $5, $7, $9, $11, $13);}
  | TUPLE '<' type_spec ',' type_spec ',' type_spec ',' type_spec ',' type_spec  ',' type_spec ',' type_spec  '>'  {$$ = new MvType(4, $3, $5, $7, $9, $11, $13, $15);}
| TUPLE '<' type_spec ',' type_spec ',' type_spec ',' type_spec ',' type_spec  ',' type_spec ',' type_spec  ',' type_spec '>'  {$$ = new MvType(4, $3, $5, $7, $9, $11, $13, $15, $17);}
  ;

//*************************************************************************************
// Expressions
//*************************************************************************************

primary_expression
  : constant
  | symbol_ref
  | funcall
  | '(' expression ')'  {$$ = $2; $$->needsParens = true;}
  ;

constant
  : integer
  | boolean
  ;

integer
: NAT {$$ = new Integer($1);}
  | '-' NAT
    {
     char *name = new char[strlen($2)+2];
     strcpy(name+1, $2);
     name[0] = '-';
     $$ = new Integer(name);
    }
  ;

boolean
: TRUE  {$$ = &b_true;}
| FALSE {$$ =&b_false;}
  ;

symbol_ref
  : ID
    {
      SymDec *s = symTab->find($1);
      if (s) {
        $$ = new SymRef(s);
      }
      else {
        yyerror("Unknown symbol");
      }
    }

  ;

funcall
  : ID '(' expr_list ')'
    {
      FunDef *f;
      if ((f = prog.funDefs->find($1)) == NULL && (f = builtins->find($1)) == NULL) {
        yyerror("Undefined function");
      }
      else {
        $$ = new FunCall(f, $3);
      }
    }
  | TEMPLATEID '<' arith_expr_list '>' '(' arith_expr_list ')'
    {
      Template *f;
      if ((f = (Template*)prog.funDefs->find($1)) == NULL) {
        yyerror("Undefined function template");
      }
      else {
        $$ = new TempCall(f, $6, $3);
      }
    }
  ;

postfix_expression
  : primary_expression
  | array_or_bit_ref
  | struct_ref
  | subrange
  ;

// In order to distinguish between a bit reference and a (syntactically equivalent) array
// reference, the base must be examined:

array_or_bit_ref
  : postfix_expression '[' expression ']'
    {
      if ($1->isArrayParam()) {
        $$ = new ArrayParamRef((SymRef*)$1, $3);
      }
      else if ($1->isArray()) {
        $$ = new ArrayRef($1, $3);
      }
      else {
        $$ = new BitRef($1, $3);
      }
    }
  ;

struct_ref
  : postfix_expression '.' ID  {$$ = new StructRef($1, $3);}

subrange
  : postfix_expression '.' SLC '<' NAT '>' '(' expression ')'
    {
      uint diff = (new Integer($5))->evalConst() - 1;
      if ($8->isConst()) {
        $$ = new Subrange($1, new Integer($8->evalConst() + diff), $8, (new Integer($5))->evalConst());
      }
      else {
        $$ = new Subrange($1, new BinaryExpr($8, new Integer(diff), newstr("+")), $8, (new Integer($5))->evalConst());
      }
    }

prefix_expression
  : postfix_expression
  | unary_op prefix_expression           {$$ = new PrefixExpr($2, $1);}
  | '(' type_spec ')' prefix_expression  {$$ = new CastExpr($4, $2);}
  | type_spec '(' expression  ')'        {$$ = new CastExpr($3, $1);}
  ;

unary_op
  : '+'
  | '-'
  | '~'
  | '!'
  ;

mult_expression
  : prefix_expression
  | mult_expression '*' prefix_expression  {$$ = new BinaryExpr($1, $3, $2);}
  | mult_expression '/' prefix_expression  {$$ = new BinaryExpr($1, $3, $2);}
  | mult_expression '%' prefix_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

add_expression
  : mult_expression
  | add_expression '+' mult_expression  {$$ = new BinaryExpr($1, $3, $2);}
  | add_expression '-' mult_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

arithmetic_expression
  : add_expression
  | arithmetic_expression LSHFT_OP add_expression  {$$ = new BinaryExpr($1, $3, $2);}
  | arithmetic_expression RSHFT_OP add_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

rel_expression
  : arithmetic_expression
  | rel_expression '<' arithmetic_expression    {$$ = new BinaryExpr($1, $3, $2);}
  | rel_expression '>' arithmetic_expression    {$$ = new BinaryExpr($1, $3, $2);}
  | rel_expression LE_OP arithmetic_expression  {$$ = new BinaryExpr($1, $3, $2);}
  | rel_expression GE_OP arithmetic_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

eq_expression
  : rel_expression
  | eq_expression EQ_OP rel_expression  {$$ = new BinaryExpr($1, $3, $2);}
  | eq_expression NE_OP rel_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

and_expression
  : eq_expression
  | and_expression '&' eq_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

xor_expression
  : and_expression
  | xor_expression '^' and_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

ior_expression
  : xor_expression
  | ior_expression '|' xor_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

log_and_expression
  : ior_expression
  | log_and_expression AND_OP ior_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

log_or_expression
  : log_and_expression
  | log_or_expression OR_OP log_and_expression  {$$ = new BinaryExpr($1, $3, $2);}
  ;

cond_expression
  : log_or_expression
  | log_or_expression '?' expression ':' cond_expression  {$$ = new CondExpr($3, $5, $1);}
  ;

mv_expression
  : mv_type '(' expr_list ')' {$$ = new MultipleValue((MvType*)$1, $3);}
  ;

expression
  : cond_expression
  | mv_expression
  ;

expr_list
  :                     {$$ = NULL;}
| nontrivial_expr_list  {$$ = $1;}
  ;

nontrivial_expr_list
  : expression                           {$$ = new List<Expression>($1);}
  | nontrivial_expr_list ',' expression  {$$ = $1->add($3);}
  ;


arith_expr_list
  :                     {$$ = NULL;}
| nontrivial_arith_expr_list  {$$ = $1;}
  ;

nontrivial_arith_expr_list
  : arithmetic_expression                                 {$$ = new List<Expression>($1);}
  | nontrivial_arith_expr_list ',' arithmetic_expression  {$$ = $1->add($3);}
  ;


//*************************************************************************************
// Statements
//*************************************************************************************

statement
  : simple_statement ';'
  | block
  | for_statement
  | if_statement
  | switch_statement
  ;

r_statement
  : final_statement
  | r_block
  ;

simple_statement
  : var_dec
  | const_dec
  | multiple_var_dec
  | multiple_const_dec
  | break_statement
  | assignment
  | multiple_assignment
  | assertion
  | null_statement
  ;

var_dec
  : type_spec untyped_var_dec
    {
     $$ = $2;
     Type *t = ((VarDec*)$$)->type;
       if (t) {
       ((ArrayType*)t)->baseType = $1;
     }
     else {
       ((VarDec*)$$)->type = $1;
     }
    }
  ;

untyped_var_dec
  : ID
    {$$ = new VarDec($1, NULL); symTab->push((VarDec*)$$);}
  | ID '=' expression
    {$$ = new VarDec($1, NULL, $3); symTab->push((VarDec*)$$);}
  | ID '=' array_init
    {$$ = new VarDec($1, NULL, $3); symTab->push((VarDec*)$$);}
  | ID '[' arithmetic_expression ']'
    {
      if ($3->isConst() && $3->evalConst() > 0) {
        $$ = new VarDec($1, new ArrayType($3, NULL)); symTab->push((VarDec*)$$);
      }
      else {
        yyerror("Non-constant array dimension");
      }
    }
  | ID '[' arithmetic_expression ']' '=' array_init
    {
      if ($3->isConst() && $3->evalConst() > 0) {
        $$ = new VarDec($1, new ArrayType($3, NULL), $6); symTab->push((VarDec*)$$);
      }
      else {
        yyerror("Non-constant array dimension");
      }
    }
  ;

array_init
  : '{' array_init_list '}'  {$$ = new Initializer((List<Constant>*)($2->front));}
  ;

array_init_list
  : expression                      {$$ = new BigList<Expression>($1);}
  | array_init_list ',' expression  {$$ = $1->add($3);}
  ;

const_dec
  : CONST type_spec untyped_const_dec
    {
     $$ = $3;
     Type *t = ((ConstDec*)$$)->type;
       if (t) {
       ((ArrayType*)t)->baseType = $2;
     }
     else {
       ((ConstDec*)$$)->type = $2;
     }
    }
  ;

untyped_const_dec
  : ID '=' expression
    {$$ = new ConstDec($1, NULL, $3); symTab->push((ConstDec*)$$);}
  | ID '=' array_init
    {$$ = new ConstDec($1, NULL, $3); symTab->push((ConstDec*)$$);}
  | ID '[' arithmetic_expression ']' '=' array_init
    {
      if ($3->isConst() && $3->evalConst() > 0) {
        $$ = new ConstDec($1, new ArrayType($3, NULL), $6); symTab->push((ConstDec*)$$);
      }
      else {
        yyerror("Non-constant array dimension");
      }
    }
  ;

multiple_var_dec
  : var_dec ',' untyped_var_dec
    {
     if (((VarDec*)$3)->type) {
       ((ArrayType*)(((VarDec*)$3)->type))->baseType = ((ArrayType*)(((VarDec*)$1)->type))->baseType;
     }
     else {
       ((VarDec*)$3)->type = ((VarDec*)$1)->type;
     }
     $$ = new MulVarDec((VarDec*)$1, (VarDec*)$3);
    }
  | multiple_var_dec ',' untyped_var_dec
    {
     if (((VarDec*)$3)->type) {
       ((ArrayType*)(((VarDec*)$3)->type))->baseType = ((ArrayType*)((MulVarDec*)$1)->decs->value->type)->baseType;
     }
     else {
       ((VarDec*)$3)->type = ((MulVarDec*)$1)->decs->value->type;
     }
     $$ = $1;
     ((MulVarDec*)$$)->decs->add((VarDec*)$3);
    }
  ;

multiple_const_dec
  : const_dec ',' untyped_const_dec
    {
     if (((ConstDec*)$3)->type) {
       ((ArrayType*)(((ConstDec*)$3)->type))->baseType = ((ArrayType*)(((ConstDec*)$1)->type))->baseType;
     }
     else {
       ((ConstDec*)$3)->type = ((ConstDec*)$1)->type;
     }
     $$ = new MulConstDec((ConstDec*)$1, (ConstDec*)$3);
    }
  | multiple_const_dec ',' untyped_const_dec
    {
     if (((ConstDec*)$3)->type) {
       ((ArrayType*)(((ConstDec*)$3)->type))->baseType = ((ArrayType*)((MulConstDec*)$1)->decs->value->type)->baseType;
     }
     else {
       ((ConstDec*)$3)->type = ((MulConstDec*)$1)->decs->value->type;
     }
     $$ = $1;
     ((MulConstDec*)$$)->decs->add((ConstDec*)$3);
    }
  ;

break_statement
  : BREAK     {$$ = &breakStmt;}
  ;

return_statement
  : RETURN             {$$ = new ReturnStmt(NULL);}
  | RETURN expression  {$$ = new ReturnStmt($2);}
  ;

assignment
  : expression assign_op expression {$$ = new Assignment($1, $2, $3);}
  | expression inc_op               {$$ = new Assignment($1, $2, NULL);}
  | postfix_expression '.' SET_SLC '(' expression ',' expression ')'
  {
   uint w = 0;
   if ($7->isSubrange()) {
     w = ((Subrange*)$7)->width;
   }
   else {
     Type *type = $7->exprType();
     if (type) {
       type = type->derefType();
       if (type->isRegType()) {
         w = ((RegType*)type)->width->evalConst();
       }
     }
   }
   if (w == 0) {
     yyerror("Second arg of set_slc must have a defined width");
   }
   else {
     Expression *top;
     if ($5->isConst()) {
       top = new Integer($5->evalConst() + w - 1);
     }
     else {
       top = new BinaryExpr($5, new Integer(w - 1), newstr("+"));
     }
     $$ = new Assignment(new Subrange($1, top, $5), "=", $7);
   }
  }
  ;

assign_op
  : '='
  | RSHFT_ASSIGN
  | LSHFT_ASSIGN
  | ADD_ASSIGN
  | SUB_ASSIGN
  | MUL_ASSIGN
  | MOD_ASSIGN
  | AND_ASSIGN
  | XOR_ASSIGN
  | OR_ASSIGN
  ;

inc_op
  : INC_OP
  | DEC_OP
  ;

multiple_assignment
  : TIE '(' nontrivial_expr_list ')' '=' postfix_expression
    {$$ = new MultipleAssignment((FunCall*)$6, $3);}
  ;

assertion
  : ASSERT '(' expression ')'  {$$ = new Assertion($3);}
  ;

null_statement
  : {$$ = new NullStmt;}
  ;

dummy
  : {symTab->pushFrame();}
  ;

block
  : '{' dummy statement_list '}'  {symTab->popFrame(); $$ = new Block($3);}
  ; // Replace 'dummy' with the midrule action '{symTab->pushFrame();}'
    // will cause reduce/reduce conflicts.

r_block
  : '{' dummy r_statement_list '}'  {symTab->popFrame(); $$ = new Block($3);}
  ; // Replace 'dummy' with the midrule action '{symTab->pushFrame();}'
    // will cause reduce/reduce conflicts.

statement_list
  : {$$ = NULL;}
  | statement_list statement  {$$ = $1 ? $1->add($2) : new List<Statement>($2);}
  ;

r_statement_list
  : statement_list final_statement  {$$ = $1 ? $1->add($2) : new List<Statement>($2);}
  ;

for_statement
  : FOR {symTab->pushFrame();} '(' for_init ';' expression ';' assignment ')'
    statement
    {
      $$ = new ForStmt((SimpleStatement*)$4, $6, (Assignment*)$8, $10);
      symTab->popFrame();
    }
  ;

for_init
  : var_dec {symTab->push((VarDec*)$1);}
  | assignment
  ;

if_statement
  : IF '(' expression ')' statement                 {$$ = new IfStmt($3, $5, NULL);}
  | IF '(' expression ')' statement ELSE statement  {$$ = new IfStmt($3, $5, $7);}
  ;

switch_statement
  : SWITCH '(' expression ')' '{' case_list '}'  {$$ = new SwitchStmt($3, $6);}
  ;

case_list
  : case            {$$ = new List<Case>($1);}
  | case_list case  {$$ = $1->add($2);}
  ;

case
  : CASE case_label ':' statement_list  {$$ = new Case($2, $4);}
  | DEFAULT ':' statement_list          {$$ = new Case(NULL, $3);}
  ;

case_label
  : constant
  | symbol_ref
    {
      if ($1->exprType()->isEnumType()) {
        $$ = $1;
      }
      else {
        yyerror("case label must be an integer or an enum constant");
      }
    }

final_statement
  : return_statement ';'
  | IF '(' expression ')' r_statement ELSE r_statement  {$$ = new IfStmt($3, $5, $7);}
  ;

//*************************************************************************************
// Function Definitions
//*************************************************************************************

func_def
  : type_spec ID {symTab->pushFrame();} '(' param_dec_list ')' r_block
    {$$ = new FunDef($2, $1, $5, (Block*)$7); symTab->popFrame();}
  | func_template
  ;

param_dec_list
  : {$$ = NULL;}
  | nontrivial_param_dec_list
  ;

nontrivial_param_dec_list
  : var_dec                                {$$ = new List<VarDec>((VarDec*)$1);}
  | nontrivial_param_dec_list ',' var_dec  {$$ = $1->add((VarDec*)$3);}
  ;

func_template
  : TEMPLATE {symTab->pushFrame();} '<' template_param_dec_list '>'
    type_spec ID '(' param_dec_list ')' r_block
    {
      $$ = new Template($7, $6, $9, (Block*)$11, $4); symTab->popFrame();
      if (!prog.templates) {
        prog.templates = new List<Template>((Template*)$$);
      }
      else {
        prog.templates->add((Template*)$$);
      }
    }
  ;

template_param_dec_list
  : {$$ = NULL;}
  | nontrivial_template_param_dec_list
  ;

nontrivial_template_param_dec_list
  : template_param_dec                                         {$$ = new List<TempParamDec>((TempParamDec*)$1);}
  | nontrivial_template_param_dec_list ',' template_param_dec  {$$ = $1->add((TempParamDec*)$3);}
  ;

template_param_dec
: type_spec ID {$$ = new TempParamDec($2, $1);symTab->push((TempParamDec*)$$);}
  ;

%%

#include <stdio.h>

void yyerror(const char *s) {
  fflush(stdout);
  fprintf(stderr, "%s:%d: %s\n", yyfilenm, yylineno, s);
}
