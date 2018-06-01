/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton interface for Bison's Yacc-like parsers in C

   Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.

   This program is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, write to the Free Software
   Foundation, Inc., 51 Franklin Street, Fifth Floor,
   Boston, MA 02110-1301, USA.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     TYPEDEF = 258,
     CONST = 259,
     STRUCT = 260,
     ENUM = 261,
     TEMPLATE = 262,
     MASC = 263,
     INT = 264,
     UINT = 265,
     INT64 = 266,
     UINT64 = 267,
     BOOL = 268,
     TO_UINT = 269,
     TO_UINT64 = 270,
     RANGE = 271,
     SLC = 272,
     SET_SLC = 273,
     WAIT = 274,
     FOR = 275,
     IF = 276,
     ELSE = 277,
     WHILE = 278,
     DO = 279,
     SWITCH = 280,
     CASE = 281,
     DEFAULT = 282,
     BREAK = 283,
     CONTINUE = 284,
     RETURN = 285,
     ASSERT = 286,
     ARRAY = 287,
     TUPLE = 288,
     TIE = 289,
     SC_INT = 290,
     SC_BIGINT = 291,
     SC_FIXED = 292,
     SC_UINT = 293,
     SC_BIGUINT = 294,
     SC_UFIXED = 295,
     AC_INT = 296,
     RSHFT_ASSIGN = 297,
     LSHFT_ASSIGN = 298,
     ADD_ASSIGN = 299,
     SUB_ASSIGN = 300,
     MUL_ASSIGN = 301,
     MOD_ASSIGN = 302,
     AND_ASSIGN = 303,
     XOR_ASSIGN = 304,
     OR_ASSIGN = 305,
     INC_OP = 306,
     DEC_OP = 307,
     RSHFT_OP = 308,
     LSHFT_OP = 309,
     AND_OP = 310,
     OR_OP = 311,
     LE_OP = 312,
     GE_OP = 313,
     EQ_OP = 314,
     NE_OP = 315,
     ID = 316,
     NAT = 317,
     TRUE = 318,
     FALSE = 319,
     TYPEID = 320,
     TEMPLATEID = 321
   };
#endif
/* Tokens.  */
#define TYPEDEF 258
#define CONST 259
#define STRUCT 260
#define ENUM 261
#define TEMPLATE 262
#define MASC 263
#define INT 264
#define UINT 265
#define INT64 266
#define UINT64 267
#define BOOL 268
#define TO_UINT 269
#define TO_UINT64 270
#define RANGE 271
#define SLC 272
#define SET_SLC 273
#define WAIT 274
#define FOR 275
#define IF 276
#define ELSE 277
#define WHILE 278
#define DO 279
#define SWITCH 280
#define CASE 281
#define DEFAULT 282
#define BREAK 283
#define CONTINUE 284
#define RETURN 285
#define ASSERT 286
#define ARRAY 287
#define TUPLE 288
#define TIE 289
#define SC_INT 290
#define SC_BIGINT 291
#define SC_FIXED 292
#define SC_UINT 293
#define SC_BIGUINT 294
#define SC_UFIXED 295
#define AC_INT 296
#define RSHFT_ASSIGN 297
#define LSHFT_ASSIGN 298
#define ADD_ASSIGN 299
#define SUB_ASSIGN 300
#define MUL_ASSIGN 301
#define MOD_ASSIGN 302
#define AND_ASSIGN 303
#define XOR_ASSIGN 304
#define OR_ASSIGN 305
#define INC_OP 306
#define DEC_OP 307
#define RSHFT_OP 308
#define LSHFT_OP 309
#define AND_OP 310
#define OR_OP 311
#define LE_OP 312
#define GE_OP 313
#define EQ_OP 314
#define NE_OP 315
#define ID 316
#define NAT 317
#define TRUE 318
#define FALSE 319
#define TYPEID 320
#define TEMPLATEID 321




#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
#line 17 "parser.y"
{
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
/* Line 1529 of yacc.c.  */
#line 204 "parser.tab.h"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif

extern YYSTYPE yylval;

