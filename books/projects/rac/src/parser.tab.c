/* A Bison parser, made by GNU Bison 2.3.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.3"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Using locations.  */
#define YYLSP_NEEDED 0



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




/* Copy the first part of user declarations.  */
#line 1 "parser.y"

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



/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif

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
/* Line 193 of yacc.c.  */
#line 267 "parser.tab.c"
	YYSTYPE;
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
# define YYSTYPE_IS_TRIVIAL 1
#endif



/* Copy the second part of user declarations.  */


/* Line 216 of yacc.c.  */
#line 280 "parser.tab.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int i)
#else
static int
YYID (i)
    int i;
#endif
{
  return i;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss;
  YYSTYPE yyvs;
  };

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack)					\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack, Stack, yysize);				\
	Stack = &yyptr->Stack;						\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  54
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   865

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  91
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  91
/* YYNRULES -- Number of rules.  */
#define YYNRULES  218
/* YYNRULES -- Number of states.  */
#define YYNSTATES  450

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   321

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    72,     2,     2,     2,    75,    70,     2,
      86,    87,    74,    68,    83,    69,    88,    79,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    90,    80,
      76,    67,    77,    89,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    81,     2,    82,    78,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    84,    71,    85,    73,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64,
      65,    66
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     6,     8,    11,    14,    16,    18,    22,
      26,    30,    35,    37,    39,    41,    43,    45,    47,    50,
      53,    55,    57,    59,    61,    63,    68,    73,    78,    83,
      90,    97,   104,   111,   118,   122,   124,   127,   131,   135,
     137,   141,   143,   147,   154,   163,   174,   187,   202,   219,
     221,   223,   225,   229,   231,   233,   235,   238,   240,   242,
     244,   249,   257,   259,   261,   263,   265,   267,   269,   274,
     278,   287,   297,   303,   309,   311,   314,   319,   324,   326,
     328,   330,   332,   334,   338,   342,   346,   348,   352,   356,
     358,   362,   366,   368,   372,   376,   380,   384,   386,   390,
     394,   396,   400,   402,   406,   408,   412,   414,   418,   420,
     424,   426,   432,   437,   439,   441,   442,   444,   446,   450,
     451,   453,   455,   459,   462,   464,   466,   468,   470,   478,
     480,   482,   484,   486,   488,   490,   492,   494,   496,   498,
     500,   502,   505,   507,   511,   515,   520,   527,   531,   533,
     537,   541,   545,   549,   556,   560,   564,   568,   572,   576,
     578,   580,   582,   585,   589,   592,   601,   603,   605,   607,
     609,   611,   613,   615,   617,   619,   621,   623,   625,   632,
     637,   638,   639,   644,   645,   648,   650,   652,   654,   659,
     664,   665,   676,   678,   680,   686,   694,   700,   708,   716,
     718,   721,   726,   730,   732,   734,   735,   743,   745,   746,
     748,   750,   754,   755,   767,   768,   770,   772,   776
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int16 yyrhs[] =
{
      92,     0,    -1,    93,    92,    -1,    93,    -1,    94,    80,
      -1,   145,    80,    -1,   173,    -1,    95,    -1,     5,    61,
     101,    -1,     6,    61,   104,    -1,     3,    96,    61,    -1,
      95,    81,   124,    82,    -1,    98,    -1,    99,    -1,   100,
      -1,   107,    -1,    65,    -1,    96,    -1,     5,   101,    -1,
       6,   104,    -1,     9,    -1,    10,    -1,    11,    -1,    12,
      -1,    13,    -1,    35,    76,   124,    77,    -1,    38,    76,
     124,    77,    -1,    39,    76,   124,    77,    -1,    36,    76,
     124,    77,    -1,    37,    76,   124,    83,   124,    77,    -1,
      40,    76,   124,    83,   124,    77,    -1,    41,    76,   124,
      83,    64,    77,    -1,    41,    76,   124,    83,    63,    77,
      -1,    32,    76,    97,    83,   124,    77,    -1,    84,   102,
      85,    -1,   103,    -1,   102,   103,    -1,    97,    61,    80,
      -1,    84,   105,    85,    -1,   106,    -1,   105,    83,   106,
      -1,    61,    -1,    61,    67,   134,    -1,    33,    76,    97,
      83,    97,    77,    -1,    33,    76,    97,    83,    97,    83,
      97,    77,    -1,    33,    76,    97,    83,    97,    83,    97,
      83,    97,    77,    -1,    33,    76,    97,    83,    97,    83,
      97,    83,    97,    83,    97,    77,    -1,    33,    76,    97,
      83,    97,    83,    97,    83,    97,    83,    97,    83,    97,
      77,    -1,    33,    76,    97,    83,    97,    83,    97,    83,
      97,    83,    97,    83,    97,    83,    97,    77,    -1,   109,
      -1,   112,    -1,   113,    -1,    86,   134,    87,    -1,   110,
      -1,   111,    -1,    62,    -1,    69,    62,    -1,    63,    -1,
      64,    -1,    61,    -1,    61,    86,   135,    87,    -1,    66,
      76,   137,    77,    86,   137,    87,    -1,   108,    -1,   115,
      -1,   116,    -1,   117,    -1,   118,    -1,   119,    -1,   114,
      81,   134,    82,    -1,   114,    88,    61,    -1,   114,    88,
      16,    86,   134,    83,   134,    87,    -1,   114,    88,    17,
      76,    62,    77,    86,   134,    87,    -1,   114,    88,    14,
      86,    87,    -1,   114,    88,    15,    86,    87,    -1,   114,
      -1,   121,   120,    -1,    86,    97,    87,   120,    -1,    97,
      86,   134,    87,    -1,    68,    -1,    69,    -1,    73,    -1,
      72,    -1,   120,    -1,   122,    74,   120,    -1,   122,    79,
     120,    -1,   122,    75,   120,    -1,   122,    -1,   123,    68,
     122,    -1,   123,    69,   122,    -1,   123,    -1,   124,    54,
     123,    -1,   124,    53,   123,    -1,   124,    -1,   125,    76,
     124,    -1,   125,    77,   124,    -1,   125,    57,   124,    -1,
     125,    58,   124,    -1,   125,    -1,   126,    59,   125,    -1,
     126,    60,   125,    -1,   126,    -1,   127,    70,   126,    -1,
     127,    -1,   128,    78,   127,    -1,   128,    -1,   129,    71,
     128,    -1,   129,    -1,   130,    55,   129,    -1,   130,    -1,
     131,    56,   130,    -1,   131,    -1,   131,    89,   134,    90,
     132,    -1,   107,    86,   135,    87,    -1,   132,    -1,   133,
      -1,    -1,   136,    -1,   134,    -1,   136,    83,   134,    -1,
      -1,   138,    -1,   124,    -1,   138,    83,   124,    -1,   140,
      80,    -1,   159,    -1,   162,    -1,   168,    -1,   169,    -1,
       8,   112,    61,    84,   136,    85,   139,    -1,   141,    -1,
     145,    -1,   147,    -1,   148,    -1,   149,    -1,   150,    -1,
     151,    -1,   152,    -1,   153,    -1,   156,    -1,   157,    -1,
     158,    -1,    97,   142,    -1,    61,    -1,    61,    67,   134,
      -1,    61,    67,   143,    -1,    61,    81,   124,    82,    -1,
      61,    81,   124,    82,    67,   143,    -1,    84,   144,    85,
      -1,   134,    -1,   144,    83,   134,    -1,     4,    97,   146,
      -1,    61,    67,   134,    -1,    61,    67,   143,    -1,    61,
      81,   124,    82,    67,   143,    -1,   141,    83,   142,    -1,
     147,    83,   142,    -1,   145,    83,   146,    -1,   148,    83,
     146,    -1,    19,    86,    87,    -1,    29,    -1,    28,    -1,
      30,    -1,    30,   134,    -1,   134,   154,   134,    -1,   134,
     155,    -1,   114,    88,    18,    86,   134,    83,   134,    87,
      -1,    67,    -1,    42,    -1,    43,    -1,    44,    -1,    45,
      -1,    46,    -1,    47,    -1,    48,    -1,    49,    -1,    50,
      -1,    51,    -1,    52,    -1,    34,    86,   136,    87,    67,
     114,    -1,    31,    86,   134,    87,    -1,    -1,    -1,    84,
     160,   161,    85,    -1,    -1,   161,   139,    -1,   163,    -1,
     166,    -1,   167,    -1,     8,   109,    61,   162,    -1,     8,
     112,    61,   162,    -1,    -1,    20,   164,    86,   165,    80,
     134,    80,   153,    87,   139,    -1,   141,    -1,   153,    -1,
      23,    86,   134,    87,   139,    -1,    24,   139,    23,    86,
     134,    87,    80,    -1,    21,    86,   134,    87,   139,    -1,
      21,    86,   134,    87,   139,    22,   139,    -1,    25,    86,
     134,    87,    84,   170,    85,    -1,   171,    -1,   170,   171,
      -1,    26,   172,    90,   161,    -1,    27,    90,   161,    -1,
     109,    -1,   112,    -1,    -1,    97,    61,   174,    86,   175,
      87,   159,    -1,   177,    -1,    -1,   176,    -1,   141,    -1,
     176,    83,   141,    -1,    -1,     7,   178,    76,   179,    77,
      97,    61,    86,   175,    87,   159,    -1,    -1,   180,    -1,
     181,    -1,   180,    83,   181,    -1,    97,    61,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,    96,    96,    97,   101,   113,   125,   144,   145,   146,
     150,   151,   163,   164,   165,   166,   167,   171,   172,   173,
     177,   178,   179,   180,   181,   185,   194,   203,   212,   221,
     230,   239,   248,   261,   273,   277,   278,   282,   286,   290,
     291,   295,   296,   300,   301,   302,   303,   304,   305,   313,
     314,   315,   316,   320,   321,   325,   326,   336,   337,   341,
     355,   365,   378,   379,   380,   381,   382,   383,   390,   405,
     408,   409,   421,   425,   429,   430,   431,   432,   436,   437,
     438,   439,   443,   444,   445,   446,   450,   451,   452,   456,
     457,   458,   462,   463,   464,   465,   466,   470,   471,   472,
     476,   477,   481,   482,   486,   487,   491,   492,   496,   497,
     501,   502,   506,   510,   511,   515,   516,   520,   521,   526,
     527,   531,   532,   541,   542,   543,   544,   545,   546,   551,
     552,   553,   554,   555,   556,   557,   558,   559,   560,   561,
     562,   566,   580,   582,   584,   586,   595,   607,   611,   612,
     616,   630,   632,   634,   646,   656,   670,   680,   694,   698,
     702,   706,   707,   711,   712,   713,   745,   746,   747,   748,
     749,   750,   751,   752,   753,   754,   758,   759,   763,   768,
     772,   776,   776,   780,   781,   785,   786,   787,   788,   789,
     793,   793,   802,   803,   807,   811,   815,   816,   820,   824,
     825,   829,   830,   834,   835,   850,   850,   852,   856,   857,
     861,   862,   866,   866,   880,   881,   885,   886,   890
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TYPEDEF", "CONST", "STRUCT", "ENUM",
  "TEMPLATE", "MASC", "INT", "UINT", "INT64", "UINT64", "BOOL", "TO_UINT",
  "TO_UINT64", "RANGE", "SLC", "SET_SLC", "WAIT", "FOR", "IF", "ELSE",
  "WHILE", "DO", "SWITCH", "CASE", "DEFAULT", "BREAK", "CONTINUE",
  "RETURN", "ASSERT", "ARRAY", "TUPLE", "TIE", "SC_INT", "SC_BIGINT",
  "SC_FIXED", "SC_UINT", "SC_BIGUINT", "SC_UFIXED", "AC_INT",
  "RSHFT_ASSIGN", "LSHFT_ASSIGN", "ADD_ASSIGN", "SUB_ASSIGN", "MUL_ASSIGN",
  "MOD_ASSIGN", "AND_ASSIGN", "XOR_ASSIGN", "OR_ASSIGN", "INC_OP",
  "DEC_OP", "RSHFT_OP", "LSHFT_OP", "AND_OP", "OR_OP", "LE_OP", "GE_OP",
  "EQ_OP", "NE_OP", "ID", "NAT", "TRUE", "FALSE", "TYPEID", "TEMPLATEID",
  "'='", "'+'", "'-'", "'&'", "'|'", "'!'", "'~'", "'*'", "'%'", "'<'",
  "'>'", "'^'", "'/'", "';'", "'['", "']'", "','", "'{'", "'}'", "'('",
  "')'", "'.'", "'?'", "':'", "$accept", "program", "program_element",
  "type_dec", "typedef_dec", "typedef_type", "type_spec", "primitive_type",
  "register_type", "array_param_type", "struct_type", "struct_field_list",
  "struct_field", "enum_type", "enum_const_dec_list", "enum_const_dec",
  "mv_type", "primary_expression", "constant", "integer", "boolean",
  "symbol_ref", "funcall", "postfix_expression", "array_or_bit_ref",
  "struct_ref", "subrange", "to_uint_expression", "to_uint64_expression",
  "prefix_expression", "unary_op", "mult_expression", "add_expression",
  "arithmetic_expression", "rel_expression", "eq_expression",
  "and_expression", "xor_expression", "ior_expression",
  "log_and_expression", "log_or_expression", "cond_expression",
  "mv_expression", "expression", "expr_list", "nontrivial_expr_list",
  "arith_expr_list", "nontrivial_arith_expr_list", "statement",
  "simple_statement", "var_dec", "untyped_var_dec", "array_init",
  "array_init_list", "const_dec", "untyped_const_dec", "multiple_var_dec",
  "multiple_const_dec", "wait_statement", "continue_statement",
  "break_statement", "return_statement", "assignment", "assign_op",
  "inc_op", "multiple_assignment", "assertion", "null_statement", "block",
  "@1", "statement_list", "iterative_statement", "for_statement", "@2",
  "for_init", "while_statement", "do_statement", "if_statement",
  "switch_statement", "case_list", "case", "case_label", "func_def", "@3",
  "param_dec_list", "nontrivial_param_dec_list", "func_template", "@4",
  "template_param_dec_list", "nontrivial_template_param_dec_list",
  "template_param_dec", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,   320,   321,    61,    43,    45,
      38,   124,    33,   126,    42,    37,    60,    62,    94,    47,
      59,    91,    93,    44,   123,   125,    40,    41,    46,    63,
      58
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    91,    92,    92,    93,    93,    93,    94,    94,    94,
      95,    95,    96,    96,    96,    96,    96,    97,    97,    97,
      98,    98,    98,    98,    98,    99,    99,    99,    99,    99,
      99,    99,    99,   100,   101,   102,   102,   103,   104,   105,
     105,   106,   106,   107,   107,   107,   107,   107,   107,   108,
     108,   108,   108,   109,   109,   110,   110,   111,   111,   112,
     113,   113,   114,   114,   114,   114,   114,   114,   115,   116,
     117,   117,   118,   119,   120,   120,   120,   120,   121,   121,
     121,   121,   122,   122,   122,   122,   123,   123,   123,   124,
     124,   124,   125,   125,   125,   125,   125,   126,   126,   126,
     127,   127,   128,   128,   129,   129,   130,   130,   131,   131,
     132,   132,   133,   134,   134,   135,   135,   136,   136,   137,
     137,   138,   138,   139,   139,   139,   139,   139,   139,   140,
     140,   140,   140,   140,   140,   140,   140,   140,   140,   140,
     140,   141,   142,   142,   142,   142,   142,   143,   144,   144,
     145,   146,   146,   146,   147,   147,   148,   148,   149,   150,
     151,   152,   152,   153,   153,   153,   154,   154,   154,   154,
     154,   154,   154,   154,   154,   154,   155,   155,   156,   157,
     158,   160,   159,   161,   161,   162,   162,   162,   162,   162,
     164,   163,   165,   165,   166,   167,   168,   168,   169,   170,
     170,   171,   171,   172,   172,   174,   173,   173,   175,   175,
     176,   176,   178,   177,   179,   179,   180,   180,   181
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     2,     1,     2,     2,     1,     1,     3,     3,
       3,     4,     1,     1,     1,     1,     1,     1,     2,     2,
       1,     1,     1,     1,     1,     4,     4,     4,     4,     6,
       6,     6,     6,     6,     3,     1,     2,     3,     3,     1,
       3,     1,     3,     6,     8,    10,    12,    14,    16,     1,
       1,     1,     3,     1,     1,     1,     2,     1,     1,     1,
       4,     7,     1,     1,     1,     1,     1,     1,     4,     3,
       8,     9,     5,     5,     1,     2,     4,     4,     1,     1,
       1,     1,     1,     3,     3,     3,     1,     3,     3,     1,
       3,     3,     1,     3,     3,     3,     3,     1,     3,     3,
       1,     3,     1,     3,     1,     3,     1,     3,     1,     3,
       1,     5,     4,     1,     1,     0,     1,     1,     3,     0,
       1,     1,     3,     2,     1,     1,     1,     1,     7,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     2,     1,     3,     3,     4,     6,     3,     1,     3,
       3,     3,     3,     6,     3,     3,     3,     3,     3,     1,
       1,     1,     2,     3,     2,     8,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     6,     4,
       0,     0,     4,     0,     2,     1,     1,     1,     4,     4,
       0,    10,     1,     1,     5,     7,     5,     7,     7,     1,
       2,     4,     3,     1,     1,     0,     7,     1,     0,     1,
       1,     3,     0,    11,     0,     1,     1,     3,     2
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     0,     0,   212,    20,    21,    22,    23,
      24,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      16,     0,     3,     0,     7,    17,     0,    12,    13,    14,
      15,     0,     6,   207,     0,     0,     0,     0,     0,     0,
      18,     0,     0,    19,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     1,     2,     4,     0,   205,     5,
      10,     0,   150,     8,     0,     0,    35,     9,    41,     0,
      39,   214,     0,     0,    59,    55,    57,    58,     0,    78,
      79,    81,    80,     0,     0,    62,    49,    53,    54,    50,
      51,    74,    63,    64,    65,    66,    67,    82,     0,    86,
      89,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    34,    36,     0,     0,    38,     0,     0,
     215,   216,     0,     0,   115,   119,    56,     0,    15,    92,
      97,   100,   102,   104,   106,   108,   110,   113,   114,     0,
       0,     0,     0,    75,     0,     0,     0,     0,     0,     0,
       0,    25,    28,     0,    26,    27,     0,     0,    11,   208,
       0,   151,   152,     0,    37,    42,    40,   218,     0,     0,
       0,     0,   117,     0,   116,   121,     0,   120,     0,   115,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    52,     0,     0,     0,     0,     0,     0,    69,
      83,    85,    84,    87,    88,    91,    90,     0,     0,     0,
       0,     0,   210,     0,   209,   148,     0,     0,     0,   217,
      33,    43,     0,    60,     0,     0,     0,    76,     0,    95,
      96,    93,    94,    98,    99,   101,   103,   105,   107,   109,
       0,    77,    68,     0,     0,     0,     0,    29,    30,    32,
      31,   142,   141,     0,     0,     0,   147,     0,     0,     0,
     118,   119,   122,   112,     0,    72,    73,     0,     0,     0,
       0,   181,   206,   211,   149,   153,   208,    44,     0,     0,
     111,     0,     0,   143,   144,     0,   183,     0,     0,    61,
       0,     0,   145,   180,     0,    45,     0,    70,     0,     0,
       0,     0,   190,     0,     0,   180,     0,   160,   159,   161,
       0,     0,   182,     0,    74,     0,   184,     0,   129,   130,
     131,   132,   133,   134,   135,   136,   137,   138,   139,   140,
     124,   125,   185,   186,   187,   126,   127,   213,     0,    71,
     146,    59,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   162,     0,     0,     0,   167,   168,   169,   170,   171,
     172,   173,   174,   175,   176,   177,   166,     0,   164,   123,
       0,     0,     0,     0,    46,     0,     0,     0,   158,     0,
       0,     0,     0,     0,     0,     0,     0,   163,   154,   156,
     155,   157,     0,     0,   188,     0,   189,   192,   193,     0,
     180,   180,     0,     0,   179,     0,     0,    47,     0,     0,
       0,     0,   196,   194,     0,     0,     0,     0,     0,     0,
     180,     0,   180,     0,     0,     0,     0,   199,     0,   178,
       0,    48,   128,     0,   197,   195,   203,   204,     0,   183,
     198,   200,     0,     0,   183,   202,   165,   180,   201,   191
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,    21,    22,    23,    24,    25,    84,    27,    28,    29,
      40,    65,    66,    43,    69,    70,    30,    85,    86,    87,
      88,    89,    90,    91,    92,    93,    94,    95,    96,    97,
      98,    99,   100,   129,   130,   131,   132,   133,   134,   135,
     136,   137,   138,   315,   173,   174,   176,   177,   316,   317,
     318,   252,   162,   216,   319,    62,   320,   321,   322,   323,
     324,   325,   326,   367,   368,   327,   328,   329,   330,   286,
     293,   331,   332,   346,   399,   333,   334,   335,   336,   426,
     427,   438,    32,   109,   213,   214,    33,    44,   119,   120,
     121
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -374
static const yytype_int16 yypact[] =
{
     800,   251,   208,   -52,   -40,  -374,  -374,  -374,  -374,  -374,
    -374,   -59,   -47,   -38,   -29,    36,    89,   140,   156,   162,
    -374,   121,   800,    97,   112,  -374,   190,  -374,  -374,  -374,
    -374,   178,  -374,  -374,   192,   183,   185,   211,   183,   208,
    -374,   185,   213,  -374,   201,   208,   208,   716,   716,   716,
     716,   716,   716,   716,  -374,  -374,  -374,   716,  -374,  -374,
    -374,    -1,  -374,  -374,   234,   758,  -374,  -374,   242,    45,
    -374,   208,   221,   229,   231,  -374,  -374,  -374,   245,  -374,
     260,  -374,  -374,   716,   240,  -374,  -374,  -374,  -374,  -374,
    -374,   -58,  -374,  -374,  -374,  -374,  -374,  -374,   716,   133,
     128,    64,    84,    19,    95,   113,    28,    37,    33,   241,
     674,   716,   243,  -374,  -374,   716,   213,  -374,   264,   253,
     248,  -374,   716,   208,   716,   716,  -374,   193,   246,   228,
      98,   239,   258,   255,   263,   280,   -13,  -374,  -374,   249,
     716,   716,    47,  -374,   716,   716,   716,   716,   716,   716,
     716,  -374,  -374,   716,  -374,  -374,   716,   237,  -374,   208,
     716,  -374,  -374,    40,  -374,  -374,  -374,  -374,   208,   208,
     117,    24,  -374,   250,   259,   228,   266,   261,   716,   716,
     716,   716,   716,   716,   716,   716,   716,   716,   716,   716,
     716,   716,  -374,   254,   265,   267,   268,   269,   273,  -374,
    -374,  -374,  -374,   133,   133,   128,   128,   138,   149,   275,
     279,   284,  -374,   270,   278,  -374,   101,   283,   297,  -374,
    -374,  -374,   208,  -374,   716,   281,   716,  -374,   272,   228,
     228,   228,   228,    98,    98,   239,   258,   255,   263,   280,
     274,  -374,  -374,   282,   285,   716,   300,  -374,  -374,  -374,
    -374,     8,  -374,   287,   208,   716,  -374,   289,   288,    75,
    -374,   716,   228,  -374,   716,  -374,  -374,   293,   291,   674,
     716,  -374,  -374,  -374,  -374,  -374,   208,  -374,   208,   290,
    -374,   716,   292,  -374,  -374,    52,  -374,   294,   118,  -374,
     295,   716,   313,   466,   287,  -374,   208,  -374,   296,   289,
     173,   311,  -374,   312,   316,   632,   317,  -374,  -374,   716,
     318,   319,  -374,     6,   -11,   343,  -374,   327,   326,   328,
     329,   330,  -374,  -374,  -374,  -374,  -374,  -374,  -374,  -374,
    -374,  -374,  -374,  -374,  -374,  -374,  -374,  -374,   123,  -374,
    -374,  -374,   260,   338,   353,   331,   333,   716,   716,   392,
     716,  -374,   716,   716,    39,  -374,  -374,  -374,  -374,  -374,
    -374,  -374,  -374,  -374,  -374,  -374,  -374,   716,  -374,  -374,
     284,   211,   284,   211,  -374,   208,   116,    11,  -374,   716,
     334,   336,   339,   340,   341,    67,   344,  -374,  -374,  -374,
    -374,  -374,   127,   173,  -374,   716,  -374,  -374,  -374,   337,
     632,   632,   716,   332,  -374,   359,   716,  -374,   208,   368,
     146,   716,   409,  -374,   345,   276,   119,   350,   357,   116,
     632,   355,   632,   356,   173,   347,    14,  -374,   716,   -58,
     716,  -374,  -374,   716,  -374,  -374,  -374,  -374,   348,  -374,
    -374,  -374,   352,   354,  -374,   549,  -374,   632,   549,  -374
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -374,   418,  -374,  -374,  -374,   441,     0,  -374,  -374,  -374,
     405,  -374,   379,   408,  -374,   335,   -82,  -374,  -297,  -374,
    -374,  -295,  -374,  -269,  -374,  -374,  -374,  -374,  -374,   -94,
    -374,   160,   161,   -37,   130,   271,   277,   262,   257,   298,
    -374,   188,  -374,   115,   301,  -326,   194,  -374,  -287,  -374,
    -151,  -120,  -220,  -374,   104,  -114,  -374,  -374,  -374,  -374,
    -374,  -374,  -373,  -374,  -374,  -374,  -374,  -374,  -246,  -374,
    -282,  -351,  -374,  -374,  -374,  -374,  -374,  -374,  -374,  -374,
      27,  -374,  -374,  -374,   180,  -374,  -374,  -374,  -374,  -374,
     304
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -181
static const yytype_int16 yytable[] =
{
      26,   128,    37,   343,   143,   344,   398,   272,   212,    38,
     101,   102,   103,   104,   105,   106,   107,    45,   349,   393,
     108,    41,    26,   141,   314,   394,   396,   385,   128,    46,
     142,   302,    39,   128,   304,   305,   314,   275,    47,    64,
     424,   425,   128,   190,    42,    72,    73,    48,   337,   284,
     200,   201,   202,   195,   196,   197,   198,   386,   128,   128,
     443,   195,   196,   197,   198,    64,   110,   251,   396,   410,
     141,   118,   149,   150,   163,   269,   191,   354,   128,   340,
     111,   149,   150,   127,   227,   170,   149,   150,   175,   270,
     149,   150,   140,   149,   150,   395,   343,   128,   409,   440,
     199,   221,   153,   273,    31,   149,   150,   222,   199,   128,
     314,   156,    49,   412,   413,   158,   207,   149,   150,   208,
     157,    54,   217,   171,   393,   212,    31,   436,   116,   437,
     117,   314,   314,   432,   292,   434,   302,   149,   150,   304,
     305,   151,   128,   229,   230,   231,   232,   429,   149,   150,
     224,   314,   277,   314,   405,   180,   181,   445,   278,   211,
     449,   152,   448,   128,   314,    50,   149,   150,   218,   118,
     149,   150,   154,   128,   182,   183,   314,    56,   314,   314,
      74,    75,    76,    77,   255,    78,   256,   128,   342,   262,
     155,   149,   150,    57,   220,   295,   147,   148,   139,   128,
     374,   296,   149,   150,   407,   428,   375,   144,   145,   128,
     408,   128,   146,    35,    36,   247,    51,     6,     7,     8,
       9,    10,   259,   128,   175,   161,   248,   128,   397,   224,
     165,   420,    52,   285,   341,    75,    76,    77,    53,   172,
      11,    12,   342,    13,    14,    15,    16,    17,    18,    19,
     388,    58,   390,    60,   211,   193,   194,   389,    59,   391,
       6,     7,     8,     9,    10,   128,   128,    39,   128,    42,
     128,   128,    61,    20,    68,   215,   211,    71,   288,   140,
     178,   149,   150,    11,    12,   128,    13,    14,    15,    16,
      17,    18,    19,   313,   172,   112,   338,   128,   184,   185,
     209,   210,   424,   425,   122,   313,   240,   203,   204,   115,
     205,   206,   123,   128,   233,   234,    20,   124,   128,   128,
     128,   125,   126,   164,   128,   167,   140,   159,   186,   128,
     168,   169,   179,   187,   188,   189,   192,   223,   128,   260,
     128,   241,   224,   225,   226,   251,   128,   242,   128,   246,
     257,   128,   249,   243,   244,   245,   250,   253,   258,   263,
     267,   254,   268,   128,   264,   128,   128,   261,   282,   265,
     274,   271,   266,   160,   276,   392,   281,   289,   291,   313,
     299,   294,   297,   339,   283,   355,   356,   357,   358,   359,
     360,   361,   362,   363,   364,   365,   290,   345,   347,   376,
     313,   313,   348,   350,   352,   353,   298,   369,   418,   370,
     366,   371,   372,   373,   377,   382,   415,   411,   378,   379,
     313,   400,   313,   401,   351,   402,   416,   403,   404,   419,
     406,   422,   423,   430,   431,   433,   435,   439,   444,   446,
      55,   447,    34,    63,   114,   313,   238,   313,   313,    67,
     237,   166,   280,   441,     0,   279,   287,   235,     0,     0,
       0,     0,   380,   381,   236,   383,     0,   384,   172,     0,
       2,    35,    36,   219,   300,     6,     7,     8,     9,    10,
     228,     0,   387,     0,     0,   301,   302,   303,   239,   304,
     305,   306,     0,     0,   307,   308,   309,   310,    11,    12,
     311,    13,    14,    15,    16,    17,    18,    19,     0,     0,
     172,     0,     0,     0,     0,     0,     0,   414,     0,     0,
       0,   417,     0,     0,     0,     0,   421,    74,    75,    76,
      77,    20,    78,     0,    79,    80,     0,     0,    81,    82,
       0,     0,     0,   139,     0,   442,     0,     0,     0,     0,
     271,   312,    83,     2,    35,    36,     0,   300,     6,     7,
       8,     9,    10,     0,     0,     0,     0,     0,   301,   302,
     303,     0,   304,   305,   306,     0,     0,   307,   308,   309,
     310,    11,    12,   311,    13,    14,    15,    16,    17,    18,
      19,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
      74,    75,    76,    77,    20,    78,     0,    79,    80,     0,
       0,    81,    82,     0,     0,     0,     0,     0,     0,  -180,
       0,     0,     0,   271,     0,    83,     2,    35,    36,     0,
     300,     6,     7,     8,     9,    10,     0,     0,     0,     0,
       0,   301,   302,   303,     0,   304,   305,   306,     0,     0,
     307,   308,   309,   310,    11,    12,   311,    13,    14,    15,
      16,    17,    18,    19,     0,     0,     0,     0,     0,    35,
      36,     0,     0,     6,     7,     8,     9,    10,     0,     0,
       0,     0,     0,    74,    75,    76,    77,    20,    78,     0,
      79,    80,     0,     0,    81,    82,    11,    12,     0,    13,
      14,    15,    16,    17,    18,    19,   271,     0,    83,     0,
       0,    35,    36,     0,     0,     6,     7,     8,     9,    10,
       0,     0,     0,     0,     0,    74,    75,    76,    77,    20,
      78,     0,    79,    80,     0,     0,    81,    82,    11,    12,
       0,    13,    14,    15,    16,    17,    18,    19,   160,     0,
      83,     0,     0,    35,    36,     0,     0,     6,     7,     8,
       9,    10,     0,     0,     0,     0,     0,    74,    75,    76,
      77,    20,    78,     0,    79,    80,     0,     0,    81,    82,
      11,    12,     0,    13,    14,    15,    16,    17,    18,    19,
       0,     0,    83,     1,     2,     3,     4,     5,     0,     6,
       7,     8,     9,    10,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    20,     0,     0,     0,     0,     0,     0,
       0,     0,    11,    12,     0,    13,    14,    15,    16,    17,
      18,    19,     0,   113,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    20
};

static const yytype_int16 yycheck[] =
{
       0,    83,     2,   300,    98,   300,   379,   253,   159,    61,
      47,    48,    49,    50,    51,    52,    53,    76,   305,     8,
      57,    61,    22,    81,   293,   376,   377,   353,   110,    76,
      88,    20,    84,   115,    23,    24,   305,   257,    76,    39,
      26,    27,   124,    56,    84,    45,    46,    76,   294,   269,
     144,   145,   146,    14,    15,    16,    17,    18,   140,   141,
     433,    14,    15,    16,    17,    65,    67,    61,   419,   395,
      81,    71,    53,    54,   111,    67,    89,    88,   160,   299,
      81,    53,    54,    83,   178,   122,    53,    54,   125,    81,
      53,    54,    86,    53,    54,    84,   393,   179,   393,    85,
      61,    77,    83,   254,     0,    53,    54,    83,    61,   191,
     379,    83,    76,   400,   401,    82,   153,    53,    54,   156,
      83,     0,    82,   123,     8,   276,    22,   424,    83,   424,
      85,   400,   401,   420,    82,   422,    20,    53,    54,    23,
      24,    77,   224,   180,   181,   182,   183,   416,    53,    54,
      83,   420,    77,   422,    87,    57,    58,   439,    83,   159,
     447,    77,   444,   245,   433,    76,    53,    54,   168,   169,
      53,    54,    77,   255,    76,    77,   445,    80,   447,   448,
      61,    62,    63,    64,    83,    66,    85,   269,    69,   226,
      77,    53,    54,    81,    77,    77,    68,    69,    83,   281,
      77,    83,    53,    54,    77,    86,    83,    74,    75,   291,
      83,   293,    79,     5,     6,    77,    76,     9,    10,    11,
      12,    13,   222,   305,   261,   110,    77,   309,   379,    83,
     115,    85,    76,   270,    61,    62,    63,    64,    76,   124,
      32,    33,    69,    35,    36,    37,    38,    39,    40,    41,
     370,    61,   372,    61,   254,   140,   141,   371,    80,   373,
       9,    10,    11,    12,    13,   347,   348,    84,   350,    84,
     352,   353,    61,    65,    61,   160,   276,    76,   278,    86,
      87,    53,    54,    32,    33,   367,    35,    36,    37,    38,
      39,    40,    41,   293,   179,    61,   296,   379,    59,    60,
      63,    64,    26,    27,    83,   305,   191,   147,   148,    67,
     149,   150,    83,   395,   184,   185,    65,    86,   400,   401,
     402,    76,    62,    80,   406,    61,    86,    86,    70,   411,
      77,    83,    86,    78,    71,    55,    87,    87,   420,   224,
     422,    87,    83,    77,    83,    61,   428,    82,   430,    76,
      67,   433,    77,    86,    86,    86,    77,    87,    61,    87,
     245,    83,    62,   445,    90,   447,   448,    86,    77,    87,
     255,    84,    87,    84,    86,   375,    83,    87,    86,   379,
      67,    87,    87,    87,   269,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,   281,    86,    86,    61,
     400,   401,    86,    86,    86,    86,   291,    80,   408,    83,
      67,    83,    83,    83,    61,    23,    84,    80,    87,    86,
     420,    87,   422,    87,   309,    86,    67,    87,    87,    61,
      86,    22,    87,    83,    77,    80,    80,    90,    90,    87,
      22,    87,     1,    38,    65,   445,   189,   447,   448,    41,
     188,   116,   264,   426,    -1,   261,   276,   186,    -1,    -1,
      -1,    -1,   347,   348,   187,   350,    -1,   352,   353,    -1,
       4,     5,     6,   169,     8,     9,    10,    11,    12,    13,
     179,    -1,   367,    -1,    -1,    19,    20,    21,   190,    23,
      24,    25,    -1,    -1,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    -1,    -1,
     395,    -1,    -1,    -1,    -1,    -1,    -1,   402,    -1,    -1,
      -1,   406,    -1,    -1,    -1,    -1,   411,    61,    62,    63,
      64,    65,    66,    -1,    68,    69,    -1,    -1,    72,    73,
      -1,    -1,    -1,   428,    -1,   430,    -1,    -1,    -1,    -1,
      84,    85,    86,     4,     5,     6,    -1,     8,     9,    10,
      11,    12,    13,    -1,    -1,    -1,    -1,    -1,    19,    20,
      21,    -1,    23,    24,    25,    -1,    -1,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      61,    62,    63,    64,    65,    66,    -1,    68,    69,    -1,
      -1,    72,    73,    -1,    -1,    -1,    -1,    -1,    -1,    80,
      -1,    -1,    -1,    84,    -1,    86,     4,     5,     6,    -1,
       8,     9,    10,    11,    12,    13,    -1,    -1,    -1,    -1,
      -1,    19,    20,    21,    -1,    23,    24,    25,    -1,    -1,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    -1,    -1,    -1,    -1,    -1,     5,
       6,    -1,    -1,     9,    10,    11,    12,    13,    -1,    -1,
      -1,    -1,    -1,    61,    62,    63,    64,    65,    66,    -1,
      68,    69,    -1,    -1,    72,    73,    32,    33,    -1,    35,
      36,    37,    38,    39,    40,    41,    84,    -1,    86,    -1,
      -1,     5,     6,    -1,    -1,     9,    10,    11,    12,    13,
      -1,    -1,    -1,    -1,    -1,    61,    62,    63,    64,    65,
      66,    -1,    68,    69,    -1,    -1,    72,    73,    32,    33,
      -1,    35,    36,    37,    38,    39,    40,    41,    84,    -1,
      86,    -1,    -1,     5,     6,    -1,    -1,     9,    10,    11,
      12,    13,    -1,    -1,    -1,    -1,    -1,    61,    62,    63,
      64,    65,    66,    -1,    68,    69,    -1,    -1,    72,    73,
      32,    33,    -1,    35,    36,    37,    38,    39,    40,    41,
      -1,    -1,    86,     3,     4,     5,     6,     7,    -1,     9,
      10,    11,    12,    13,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    65,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    32,    33,    -1,    35,    36,    37,    38,    39,
      40,    41,    -1,    85,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    65
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     3,     4,     5,     6,     7,     9,    10,    11,    12,
      13,    32,    33,    35,    36,    37,    38,    39,    40,    41,
      65,    92,    93,    94,    95,    96,    97,    98,    99,   100,
     107,   145,   173,   177,    96,     5,     6,    97,    61,    84,
     101,    61,    84,   104,   178,    76,    76,    76,    76,    76,
      76,    76,    76,    76,     0,    92,    80,    81,    61,    80,
      61,    61,   146,   101,    97,   102,   103,   104,    61,   105,
     106,    76,    97,    97,    61,    62,    63,    64,    66,    68,
      69,    72,    73,    86,    97,   108,   109,   110,   111,   112,
     113,   114,   115,   116,   117,   118,   119,   120,   121,   122,
     123,   124,   124,   124,   124,   124,   124,   124,   124,   174,
      67,    81,    61,    85,   103,    67,    83,    85,    97,   179,
     180,   181,    83,    83,    86,    76,    62,    97,   107,   124,
     125,   126,   127,   128,   129,   130,   131,   132,   133,   134,
      86,    81,    88,   120,    74,    75,    79,    68,    69,    53,
      54,    77,    77,    83,    77,    77,    83,    83,    82,    86,
      84,   134,   143,   124,    80,   134,   106,    61,    77,    83,
     124,    97,   134,   135,   136,   124,   137,   138,    87,    86,
      57,    58,    76,    77,    59,    60,    70,    78,    71,    55,
      56,    89,    87,   134,   134,    14,    15,    16,    17,    61,
     120,   120,   120,   122,   122,   123,   123,   124,   124,    63,
      64,    97,   141,   175,   176,   134,   144,    82,    97,   181,
      77,    77,    83,    87,    83,    77,    83,   120,   135,   124,
     124,   124,   124,   125,   125,   126,   127,   128,   129,   130,
     134,    87,    82,    86,    86,    86,    76,    77,    77,    77,
      77,    61,   142,    87,    83,    83,    85,    67,    61,    97,
     134,    86,   124,    87,    90,    87,    87,   134,    62,    67,
      81,    84,   159,   141,   134,   143,    86,    77,    83,   137,
     132,    83,    77,   134,   143,   124,   160,   175,    97,    87,
     134,    86,    82,   161,    87,    77,    83,    87,   134,    67,
       8,    19,    20,    21,    23,    24,    25,    28,    29,    30,
      31,    34,    85,    97,   114,   134,   139,   140,   141,   145,
     147,   148,   149,   150,   151,   152,   153,   156,   157,   158,
     159,   162,   163,   166,   167,   168,   169,   159,    97,    87,
     143,    61,    69,   109,   112,    86,   164,    86,    86,   139,
      86,   134,    86,    86,    88,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    67,   154,   155,    80,
      83,    83,    83,    83,    77,    83,    61,    61,    87,    86,
     134,   134,    23,   134,   134,   136,    18,   134,   142,   146,
     142,   146,    97,     8,   162,    84,   162,   141,   153,   165,
      87,    87,    86,    87,    87,    87,    86,    77,    83,   112,
     136,    80,   139,   139,   134,    84,    67,   134,    97,    61,
      85,   134,    22,    87,    26,    27,   170,   171,    86,   114,
      83,    77,   139,    80,   139,    80,   109,   112,   172,    90,
      85,   171,   134,   153,    90,   161,    87,    87,   161,   139
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *bottom, yytype_int16 *top)
#else
static void
yy_stack_print (bottom, top)
    yytype_int16 *bottom;
    yytype_int16 *top;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; bottom <= top; ++bottom)
    YYFPRINTF (stderr, " %d", *bottom);
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      fprintf (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      fprintf (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}


/* Prevent warnings from -Wmissing-prototypes.  */

#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */



/* The look-ahead symbol.  */
int yychar;

/* The semantic value of the look-ahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*----------.
| yyparse.  |
`----------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{
  
  int yystate;
  int yyn;
  int yyresult;
  /* Number of tokens to shift before error messages enabled.  */
  int yyerrstatus;
  /* Look-ahead token as an internal (translated) token number.  */
  int yytoken = 0;
#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

  /* Three stacks and their tools:
     `yyss': related to states,
     `yyvs': related to semantic values,
     `yyls': related to locations.

     Refer to the stacks thru separate pointers, to allow yyoverflow
     to reallocate them elsewhere.  */

  /* The state stack.  */
  yytype_int16 yyssa[YYINITDEPTH];
  yytype_int16 *yyss = yyssa;
  yytype_int16 *yyssp;

  /* The semantic value stack.  */
  YYSTYPE yyvsa[YYINITDEPTH];
  YYSTYPE *yyvs = yyvsa;
  YYSTYPE *yyvsp;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  YYSIZE_T yystacksize = YYINITDEPTH;

  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;


  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY;		/* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */

  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;


	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),

		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss);
	YYSTACK_RELOCATE (yyvs);

#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;


      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     look-ahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to look-ahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a look-ahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid look-ahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the look-ahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token unless it is eof.  */
  if (yychar != YYEOF)
    yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 2:
#line 96 "parser.y"
    {;}
    break;

  case 4:
#line 102 "parser.y"
    {      
      if (!prog.typeDefs) {
        prog.typeDefs = new List<DefinedType>((yyvsp[(1) - (2)].dt));
      }
      else if (prog.typeDefs->find((yyvsp[(1) - (2)].dt)->name)) { 
        yyerror("Duplicate type definition");
      }
      else { 
        prog.typeDefs->add((yyvsp[(1) - (2)].dt));
      }
    ;}
    break;

  case 5:
#line 114 "parser.y"
    {
      if (!prog.constDecs) {
        prog.constDecs = new List<ConstDec>((ConstDec*)(yyvsp[(1) - (2)].stm));
      }
      else if (prog.constDecs->find(((ConstDec*)(yyvsp[(1) - (2)].stm))->sym->name)) { 
        yyerror("Duplicate global constant declaration");
      }
      else {
        prog.constDecs->add((ConstDec*)(yyvsp[(1) - (2)].stm));
      }
    ;}
    break;

  case 6:
#line 126 "parser.y"
    {
      if (!prog.funDefs) {
        prog.funDefs = new List<FunDef>((yyvsp[(1) - (1)].fd));
      }
      else if (prog.funDefs->find((yyvsp[(1) - (1)].fd)->sym->name)) {
        yyerror("Duplicate function definition");
      }
      else {
        prog.funDefs->add((yyvsp[(1) - (1)].fd));
      }
    ;}
    break;

  case 8:
#line 145 "parser.y"
    {(yyval.dt) = new DefinedType((yyvsp[(2) - (3)].s), (yyvsp[(3) - (3)].t));;}
    break;

  case 9:
#line 146 "parser.y"
    {(yyval.dt) = new DefinedType((yyvsp[(2) - (3)].s), (yyvsp[(3) - (3)].t));;}
    break;

  case 10:
#line 150 "parser.y"
    {(yyval.dt) = new DefinedType((yyvsp[(3) - (3)].s), (yyvsp[(2) - (3)].t));;}
    break;

  case 11:
#line 152 "parser.y"
    {
      if ((yyvsp[(3) - (4)].exp)->isConst() && (yyvsp[(3) - (4)].exp)->evalConst() > 0) {
        (yyvsp[(1) - (4)].dt)->def = new ArrayType((yyvsp[(3) - (4)].exp), (yyvsp[(1) - (4)].dt)->def); (yyval.dt) = (yyvsp[(1) - (4)].dt);
      }
      else {
        yyerror("Array dimension not a positive integer constant");
      }
    ;}
    break;

  case 16:
#line 167 "parser.y"
    {(yyval.t) = prog.typeDefs->find((yyvsp[(1) - (1)].s));;}
    break;

  case 18:
#line 172 "parser.y"
    {(yyval.t) = (yyvsp[(2) - (2)].t);;}
    break;

  case 19:
#line 173 "parser.y"
    {(yyval.t) = (yyvsp[(2) - (2)].t);;}
    break;

  case 20:
#line 177 "parser.y"
    {(yyval.t) = &intType;;}
    break;

  case 21:
#line 178 "parser.y"
    {(yyval.t) = &uintType;;}
    break;

  case 22:
#line 179 "parser.y"
    {(yyval.t) = &int64Type;;}
    break;

  case 23:
#line 180 "parser.y"
    {(yyval.t) = &uint64Type;;}
    break;

  case 24:
#line 181 "parser.y"
    {(yyval.t) = &boolType;;}
    break;

  case 25:
#line 186 "parser.y"
    {
      if ((yyvsp[(3) - (4)].exp)->isConst() && (yyvsp[(3) - (4)].exp)->isInteger() && (yyvsp[(3) - (4)].exp)->evalConst() >= 0) {
       (yyval.t) = new IntType((yyvsp[(3) - (4)].exp));
      }
      else {
        yyerror("Illegal parameter of sc_int");
      }
    ;}
    break;

  case 26:
#line 195 "parser.y"
    {
      if ((yyvsp[(3) - (4)].exp)->isConst() && (yyvsp[(3) - (4)].exp)->isInteger() && (yyvsp[(3) - (4)].exp)->evalConst() >= 0) {
       (yyval.t) = new UintType((yyvsp[(3) - (4)].exp));
      }
      else {
        yyerror("Illegal parameter of sc_uint");
      }
    ;}
    break;

  case 27:
#line 204 "parser.y"
    {
      if ((yyvsp[(3) - (4)].exp)->isConst() && (yyvsp[(3) - (4)].exp)->isInteger() && (yyvsp[(3) - (4)].exp)->evalConst() >= 0) {
       (yyval.t) = new BigUintType((yyvsp[(3) - (4)].exp));
      }
      else {
        yyerror("Illegal parameter of sc_biguint");
      }
    ;}
    break;

  case 28:
#line 213 "parser.y"
    {
      if ((yyvsp[(3) - (4)].exp)->isConst() && (yyvsp[(3) - (4)].exp)->isInteger() && (yyvsp[(3) - (4)].exp)->evalConst() >= 0) {
       (yyval.t) = new IntType((yyvsp[(3) - (4)].exp));
      }
      else {
        yyerror("Illegal parameter of sc_bigint");
      }
    ;}
    break;

  case 29:
#line 222 "parser.y"
    {
      if ((yyvsp[(3) - (6)].exp)->isConst() && (yyvsp[(3) - (6)].exp)->isInteger() && ((yyvsp[(3) - (6)].exp)->evalConst() >= 0) & (yyvsp[(5) - (6)].exp)->isConst() && (yyvsp[(5) - (6)].exp)->isInteger()) {
       (yyval.t) = new FixedType((yyvsp[(3) - (6)].exp), (yyvsp[(5) - (6)].exp));
      }
      else {
        yyerror("Illegal parameter of sc_fixed");
      }
    ;}
    break;

  case 30:
#line 231 "parser.y"
    {
      if ((yyvsp[(3) - (6)].exp)->isConst() && (yyvsp[(3) - (6)].exp)->isInteger() && ((yyvsp[(3) - (6)].exp)->evalConst() >= 0) & (yyvsp[(5) - (6)].exp)->isConst() && (yyvsp[(5) - (6)].exp)->isInteger()) {
       (yyval.t) = new UfixedType((yyvsp[(3) - (6)].exp), (yyvsp[(5) - (6)].exp));
      }
      else {
        yyerror("Illegal parameter of sc_ufixed");
      }
    ;}
    break;

  case 31:
#line 240 "parser.y"
    {
      if ((yyvsp[(3) - (6)].exp)->isConst() && (yyvsp[(3) - (6)].exp)->isInteger() && (yyvsp[(3) - (6)].exp)->evalConst() >= 0) {
       (yyval.t) = new UintType((yyvsp[(3) - (6)].exp));
      }
      else {
        yyerror("Illegal parameter of ac_int");
      }
    ;}
    break;

  case 32:
#line 249 "parser.y"
    {
      if ((yyvsp[(3) - (6)].exp)->isConst() && (yyvsp[(3) - (6)].exp)->isInteger() && (yyvsp[(3) - (6)].exp)->evalConst() >= 0) {
       (yyval.t) = new IntType((yyvsp[(3) - (6)].exp));
      }
      else {
        yyerror("Illegal parameter of ac_int");
      }
    ;}
    break;

  case 33:
#line 262 "parser.y"
    {
      if ((yyvsp[(5) - (6)].exp)->isConst() && (yyvsp[(5) - (6)].exp)->evalConst() > 0) {
        (yyval.t) = new ArrayType((yyvsp[(5) - (6)].exp), (yyvsp[(3) - (6)].t));
      }
      else {
        yyerror("Non-constant array dimension");
      }
    ;}
    break;

  case 34:
#line 273 "parser.y"
    {(yyval.t) = new StructType((yyvsp[(2) - (3)].sfl));;}
    break;

  case 35:
#line 277 "parser.y"
    {(yyval.sfl) = new List<StructField>((yyvsp[(1) - (1)].sf));;}
    break;

  case 36:
#line 278 "parser.y"
    {(yyval.sfl) = (yyvsp[(1) - (2)].sfl)->add((yyvsp[(2) - (2)].sf));;}
    break;

  case 37:
#line 282 "parser.y"
    {(yyval.sf) = new StructField((yyvsp[(1) - (3)].t), (yyvsp[(2) - (3)].s));;}
    break;

  case 38:
#line 286 "parser.y"
    {(yyval.t) = new EnumType((yyvsp[(2) - (3)].ecdl));;}
    break;

  case 39:
#line 290 "parser.y"
    {(yyval.ecdl) = new List<EnumConstDec>((yyvsp[(1) - (1)].ecd));;}
    break;

  case 40:
#line 291 "parser.y"
    {(yyval.ecdl) = (yyvsp[(1) - (3)].ecdl)->add((yyvsp[(3) - (3)].ecd));;}
    break;

  case 41:
#line 295 "parser.y"
    {(yyval.ecd) = new EnumConstDec((yyvsp[(1) - (1)].s)); symTab->push((yyval.ecd));;}
    break;

  case 42:
#line 296 "parser.y"
    {(yyval.ecd) = new EnumConstDec((yyvsp[(1) - (3)].s), (yyvsp[(3) - (3)].exp)); symTab->push((yyval.ecd));;}
    break;

  case 43:
#line 300 "parser.y"
    {(yyval.t) = new MvType(2, (yyvsp[(3) - (6)].t), (yyvsp[(5) - (6)].t));;}
    break;

  case 44:
#line 301 "parser.y"
    {(yyval.t) = new MvType(3, (yyvsp[(3) - (8)].t), (yyvsp[(5) - (8)].t), (yyvsp[(7) - (8)].t));;}
    break;

  case 45:
#line 302 "parser.y"
    {(yyval.t) = new MvType(4, (yyvsp[(3) - (10)].t), (yyvsp[(5) - (10)].t), (yyvsp[(7) - (10)].t), (yyvsp[(9) - (10)].t));;}
    break;

  case 46:
#line 303 "parser.y"
    {(yyval.t) = new MvType(4, (yyvsp[(3) - (12)].t), (yyvsp[(5) - (12)].t), (yyvsp[(7) - (12)].t), (yyvsp[(9) - (12)].t), (yyvsp[(11) - (12)].t));;}
    break;

  case 47:
#line 304 "parser.y"
    {(yyval.t) = new MvType(4, (yyvsp[(3) - (14)].t), (yyvsp[(5) - (14)].t), (yyvsp[(7) - (14)].t), (yyvsp[(9) - (14)].t), (yyvsp[(11) - (14)].t), (yyvsp[(13) - (14)].t));;}
    break;

  case 48:
#line 305 "parser.y"
    {(yyval.t) = new MvType(4, (yyvsp[(3) - (16)].t), (yyvsp[(5) - (16)].t), (yyvsp[(7) - (16)].t), (yyvsp[(9) - (16)].t), (yyvsp[(11) - (16)].t), (yyvsp[(13) - (16)].t), (yyvsp[(15) - (16)].t));;}
    break;

  case 52:
#line 316 "parser.y"
    {(yyval.exp) = (yyvsp[(2) - (3)].exp); (yyval.exp)->needsParens = true;;}
    break;

  case 55:
#line 325 "parser.y"
    {(yyval.exp) = new Integer((yyvsp[(1) - (1)].s));;}
    break;

  case 56:
#line 327 "parser.y"
    {
     char *name = new char[strlen((yyvsp[(2) - (2)].s))+2];
     strcpy(name+1, (yyvsp[(2) - (2)].s));
     name[0] = '-';
     (yyval.exp) = new Integer(name);
    ;}
    break;

  case 57:
#line 336 "parser.y"
    {(yyval.exp) = &b_true;;}
    break;

  case 58:
#line 337 "parser.y"
    {(yyval.exp) =&b_false;;}
    break;

  case 59:
#line 342 "parser.y"
    {
      SymDec *s = symTab->find((yyvsp[(1) - (1)].s));
      if (s) {
        (yyval.exp) = new SymRef(s);
      }
      else {
        yyerror("Unknown symbol");
      }
    ;}
    break;

  case 60:
#line 356 "parser.y"
    {
      FunDef *f;
      if ((f = prog.funDefs->find((yyvsp[(1) - (4)].s))) == NULL && (f = builtins->find((yyvsp[(1) - (4)].s))) == NULL) {
        yyerror("Undefined function");
      }
      else {
        (yyval.exp) = new FunCall(f, (yyvsp[(3) - (4)].expl));
      }
    ;}
    break;

  case 61:
#line 366 "parser.y"
    {
      Template *f;
      if ((f = (Template*)prog.funDefs->find((yyvsp[(1) - (7)].s))) == NULL) {
        yyerror("Undefined function template");
      }
      else {
        (yyval.exp) = new TempCall(f, (yyvsp[(6) - (7)].expl), (yyvsp[(3) - (7)].expl));
      }
    ;}
    break;

  case 68:
#line 391 "parser.y"
    {
      if ((yyvsp[(1) - (4)].exp)->isArrayParam()) {
        (yyval.exp) = new ArrayParamRef((SymRef*)(yyvsp[(1) - (4)].exp), (yyvsp[(3) - (4)].exp));
      }
        else if ((yyvsp[(1) - (4)].exp)->isArray()) {
        (yyval.exp) = new ArrayRef((yyvsp[(1) - (4)].exp), (yyvsp[(3) - (4)].exp));
      }
      else {
        (yyval.exp) = new BitRef((yyvsp[(1) - (4)].exp), (yyvsp[(3) - (4)].exp));
      }
    ;}
    break;

  case 69:
#line 405 "parser.y"
    {(yyval.exp) = new StructRef((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].s));;}
    break;

  case 70:
#line 408 "parser.y"
    {(yyval.exp) = new Subrange((yyvsp[(1) - (8)].exp), (yyvsp[(5) - (8)].exp), (yyvsp[(7) - (8)].exp));;}
    break;

  case 71:
#line 410 "parser.y"
    {
      uint diff = (new Integer((yyvsp[(5) - (9)].s)))->evalConst() - 1;
      if ((yyvsp[(8) - (9)].exp)->isConst()) {
        (yyval.exp) = new Subrange((yyvsp[(1) - (9)].exp), new Integer((yyvsp[(8) - (9)].exp)->evalConst() + diff), (yyvsp[(8) - (9)].exp), (new Integer((yyvsp[(5) - (9)].s)))->evalConst());
      }
      else {
        (yyval.exp) = new Subrange((yyvsp[(1) - (9)].exp), new BinaryExpr((yyvsp[(8) - (9)].exp), new Integer(diff), newstr("+")), (yyvsp[(8) - (9)].exp), (new Integer((yyvsp[(5) - (9)].s)))->evalConst());
      }
    ;}
    break;

  case 72:
#line 421 "parser.y"
    {(yyval.exp) = new ToUintExpr((yyvsp[(1) - (5)].exp));;}
    break;

  case 73:
#line 425 "parser.y"
    {(yyval.exp) = new ToUint64Expr((yyvsp[(1) - (5)].exp));;}
    break;

  case 75:
#line 430 "parser.y"
    {(yyval.exp) = new PrefixExpr((yyvsp[(2) - (2)].exp), (yyvsp[(1) - (2)].s));;}
    break;

  case 76:
#line 431 "parser.y"
    {(yyval.exp) = new CastExpr((yyvsp[(4) - (4)].exp), (yyvsp[(2) - (4)].t));;}
    break;

  case 77:
#line 432 "parser.y"
    {(yyval.exp) = new CastExpr((yyvsp[(3) - (4)].exp), (yyvsp[(1) - (4)].t));;}
    break;

  case 83:
#line 444 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 84:
#line 445 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 85:
#line 446 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 87:
#line 451 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 88:
#line 452 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 90:
#line 457 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 91:
#line 458 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 93:
#line 463 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 94:
#line 464 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 95:
#line 465 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 96:
#line 466 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 98:
#line 471 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 99:
#line 472 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 101:
#line 477 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 103:
#line 482 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 105:
#line 487 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 107:
#line 492 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 109:
#line 497 "parser.y"
    {(yyval.exp) = new BinaryExpr((yyvsp[(1) - (3)].exp), (yyvsp[(3) - (3)].exp), (yyvsp[(2) - (3)].s));;}
    break;

  case 111:
#line 502 "parser.y"
    {(yyval.exp) = new CondExpr((yyvsp[(3) - (5)].exp), (yyvsp[(5) - (5)].exp), (yyvsp[(1) - (5)].exp));;}
    break;

  case 112:
#line 506 "parser.y"
    {(yyval.exp) = new MultipleValue((MvType*)(yyvsp[(1) - (4)].t), (yyvsp[(3) - (4)].expl));;}
    break;

  case 115:
#line 515 "parser.y"
    {(yyval.expl) = NULL;;}
    break;

  case 116:
#line 516 "parser.y"
    {(yyval.expl) = (yyvsp[(1) - (1)].expl);;}
    break;

  case 117:
#line 520 "parser.y"
    {(yyval.expl) = new List<Expression>((yyvsp[(1) - (1)].exp));;}
    break;

  case 118:
#line 521 "parser.y"
    {(yyval.expl) = (yyvsp[(1) - (3)].expl)->add((yyvsp[(3) - (3)].exp));;}
    break;

  case 119:
#line 526 "parser.y"
    {(yyval.expl) = NULL;;}
    break;

  case 120:
#line 527 "parser.y"
    {(yyval.expl) = (yyvsp[(1) - (1)].expl);;}
    break;

  case 121:
#line 531 "parser.y"
    {(yyval.expl) = new List<Expression>((yyvsp[(1) - (1)].exp));;}
    break;

  case 122:
#line 532 "parser.y"
    {(yyval.expl) = (yyvsp[(1) - (3)].expl)->add((yyvsp[(3) - (3)].exp));;}
    break;

  case 128:
#line 547 "parser.y"
    {(yyval.stm) = (yyvsp[(7) - (7)].stm); (yyval.stm)->var = (SymRef*)(yyvsp[(2) - (7)].exp); (yyval.stm)->vals = (List<Constant>*)(yyvsp[(5) - (7)].expl);;}
    break;

  case 141:
#line 567 "parser.y"
    {
     (yyval.stm) = (yyvsp[(2) - (2)].stm);
     Type *t = ((VarDec*)(yyval.stm))->type;
       if (t) {
       ((ArrayType*)t)->baseType = (yyvsp[(1) - (2)].t);
     }
     else {
       ((VarDec*)(yyval.stm))->type = (yyvsp[(1) - (2)].t);
     }
    ;}
    break;

  case 142:
#line 581 "parser.y"
    {(yyval.stm) = new VarDec((yyvsp[(1) - (1)].s), NULL); symTab->push((VarDec*)(yyval.stm));;}
    break;

  case 143:
#line 583 "parser.y"
    {(yyval.stm) = new VarDec((yyvsp[(1) - (3)].s), NULL, (yyvsp[(3) - (3)].exp)); symTab->push((VarDec*)(yyval.stm));;}
    break;

  case 144:
#line 585 "parser.y"
    {(yyval.stm) = new VarDec((yyvsp[(1) - (3)].s), NULL, (yyvsp[(3) - (3)].exp)); symTab->push((VarDec*)(yyval.stm));;}
    break;

  case 145:
#line 587 "parser.y"
    {
      if ((yyvsp[(3) - (4)].exp)->isConst() && (yyvsp[(3) - (4)].exp)->evalConst() > 0) {
        (yyval.stm) = new VarDec((yyvsp[(1) - (4)].s), new ArrayType((yyvsp[(3) - (4)].exp), NULL)); symTab->push((VarDec*)(yyval.stm));
      }
      else {
        yyerror("Non-constant array dimension");
      }
    ;}
    break;

  case 146:
#line 596 "parser.y"
    {
      if ((yyvsp[(3) - (6)].exp)->isConst() && (yyvsp[(3) - (6)].exp)->evalConst() > 0) {
        (yyval.stm) = new VarDec((yyvsp[(1) - (6)].s), new ArrayType((yyvsp[(3) - (6)].exp), NULL), (yyvsp[(6) - (6)].exp)); symTab->push((VarDec*)(yyval.stm));
      }
      else {
        yyerror("Non-constant array dimension");
      }
    ;}
    break;

  case 147:
#line 607 "parser.y"
    {(yyval.exp) = new Initializer((List<Constant>*)((yyvsp[(2) - (3)].initl)->front));;}
    break;

  case 148:
#line 611 "parser.y"
    {(yyval.initl) = new BigList<Expression>((yyvsp[(1) - (1)].exp));;}
    break;

  case 149:
#line 612 "parser.y"
    {(yyval.initl) = (yyvsp[(1) - (3)].initl)->add((yyvsp[(3) - (3)].exp));;}
    break;

  case 150:
#line 617 "parser.y"
    {
     (yyval.stm) = (yyvsp[(3) - (3)].stm);
     Type *t = ((ConstDec*)(yyval.stm))->type;
       if (t) {
       ((ArrayType*)t)->baseType = (yyvsp[(2) - (3)].t);
     }
     else {
       ((ConstDec*)(yyval.stm))->type = (yyvsp[(2) - (3)].t);
     }
    ;}
    break;

  case 151:
#line 631 "parser.y"
    {(yyval.stm) = new ConstDec((yyvsp[(1) - (3)].s), NULL, (yyvsp[(3) - (3)].exp)); symTab->push((ConstDec*)(yyval.stm));;}
    break;

  case 152:
#line 633 "parser.y"
    {(yyval.stm) = new ConstDec((yyvsp[(1) - (3)].s), NULL, (yyvsp[(3) - (3)].exp)); symTab->push((ConstDec*)(yyval.stm));;}
    break;

  case 153:
#line 635 "parser.y"
    {
      if ((yyvsp[(3) - (6)].exp)->isConst() && (yyvsp[(3) - (6)].exp)->evalConst() > 0) {
        (yyval.stm) = new ConstDec((yyvsp[(1) - (6)].s), new ArrayType((yyvsp[(3) - (6)].exp), NULL), (yyvsp[(6) - (6)].exp)); symTab->push((ConstDec*)(yyval.stm));
      }
      else {
        yyerror("Non-constant array dimension");
      }
    ;}
    break;

  case 154:
#line 647 "parser.y"
    {
     if (((VarDec*)(yyvsp[(3) - (3)].stm))->type) {
       ((ArrayType*)(((VarDec*)(yyvsp[(3) - (3)].stm))->type))->baseType = ((ArrayType*)(((VarDec*)(yyvsp[(1) - (3)].stm))->type))->baseType;
     }
     else {
       ((VarDec*)(yyvsp[(3) - (3)].stm))->type = ((VarDec*)(yyvsp[(1) - (3)].stm))->type;
     }
     (yyval.stm) = new MulVarDec((VarDec*)(yyvsp[(1) - (3)].stm), (VarDec*)(yyvsp[(3) - (3)].stm));
    ;}
    break;

  case 155:
#line 657 "parser.y"
    {
     if (((VarDec*)(yyvsp[(3) - (3)].stm))->type) {
       ((ArrayType*)(((VarDec*)(yyvsp[(3) - (3)].stm))->type))->baseType = ((ArrayType*)((MulVarDec*)(yyvsp[(1) - (3)].stm))->decs->value->type)->baseType;
     }
     else {
       ((VarDec*)(yyvsp[(3) - (3)].stm))->type = ((MulVarDec*)(yyvsp[(1) - (3)].stm))->decs->value->type;
     }
     (yyval.stm) = (yyvsp[(1) - (3)].stm);
     ((MulVarDec*)(yyval.stm))->decs->add((VarDec*)(yyvsp[(3) - (3)].stm));
    ;}
    break;

  case 156:
#line 671 "parser.y"
    {
     if (((ConstDec*)(yyvsp[(3) - (3)].stm))->type) {
       ((ArrayType*)(((ConstDec*)(yyvsp[(3) - (3)].stm))->type))->baseType = ((ArrayType*)(((ConstDec*)(yyvsp[(1) - (3)].stm))->type))->baseType;
     }
     else {
       ((ConstDec*)(yyvsp[(3) - (3)].stm))->type = ((ConstDec*)(yyvsp[(1) - (3)].stm))->type;
     }
     (yyval.stm) = new MulConstDec((ConstDec*)(yyvsp[(1) - (3)].stm), (ConstDec*)(yyvsp[(3) - (3)].stm));
    ;}
    break;

  case 157:
#line 681 "parser.y"
    {
     if (((ConstDec*)(yyvsp[(3) - (3)].stm))->type) {
       ((ArrayType*)(((ConstDec*)(yyvsp[(3) - (3)].stm))->type))->baseType = ((ArrayType*)((MulConstDec*)(yyvsp[(1) - (3)].stm))->decs->value->type)->baseType;
     }
     else {
       ((ConstDec*)(yyvsp[(3) - (3)].stm))->type = ((MulConstDec*)(yyvsp[(1) - (3)].stm))->decs->value->type;
     }
     (yyval.stm) = (yyvsp[(1) - (3)].stm);
     ((MulConstDec*)(yyval.stm))->decs->add((ConstDec*)(yyvsp[(3) - (3)].stm));
    ;}
    break;

  case 158:
#line 694 "parser.y"
    {(yyval.stm) = new WaitStmt;;}
    break;

  case 159:
#line 698 "parser.y"
    {(yyval.stm) = new ContStmt;;}
    break;

  case 160:
#line 702 "parser.y"
    {(yyval.stm) = &breakStmt;;}
    break;

  case 161:
#line 706 "parser.y"
    {(yyval.stm) = new ReturnStmt(NULL);;}
    break;

  case 162:
#line 707 "parser.y"
    {(yyval.stm) = new ReturnStmt((yyvsp[(2) - (2)].exp));;}
    break;

  case 163:
#line 711 "parser.y"
    {(yyval.stm) = new Assignment((yyvsp[(1) - (3)].exp), (yyvsp[(2) - (3)].s), (yyvsp[(3) - (3)].exp));;}
    break;

  case 164:
#line 712 "parser.y"
    {(yyval.stm) = new Assignment((yyvsp[(1) - (2)].exp), (yyvsp[(2) - (2)].s), NULL);;}
    break;

  case 165:
#line 714 "parser.y"
    {
   uint w = 0;
   if ((yyvsp[(7) - (8)].exp)->isSubrange()) {
     w = ((Subrange*)(yyvsp[(7) - (8)].exp))->width;
   }
   else {
     Type *type = (yyvsp[(7) - (8)].exp)->exprType();
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
     if ((yyvsp[(5) - (8)].exp)->isConst()) {
       top = new Integer((yyvsp[(5) - (8)].exp)->evalConst() + w - 1);
     }
     else {
       top = new BinaryExpr((yyvsp[(5) - (8)].exp), new Integer(w - 1), newstr("+"));
     }
     (yyval.stm) = new Assignment(new Subrange((yyvsp[(1) - (8)].exp), top, (yyvsp[(5) - (8)].exp)), "=", (yyvsp[(7) - (8)].exp));
   }
  ;}
    break;

  case 178:
#line 764 "parser.y"
    {(yyval.stm) = new MultipleAssignment((FunCall*)(yyvsp[(6) - (6)].exp), (yyvsp[(3) - (6)].expl));;}
    break;

  case 179:
#line 768 "parser.y"
    {(yyval.stm) = new Assertion((yyvsp[(3) - (4)].exp));;}
    break;

  case 180:
#line 772 "parser.y"
    {(yyval.stm) = new NullStmt;;}
    break;

  case 181:
#line 776 "parser.y"
    {symTab->pushFrame();;}
    break;

  case 182:
#line 776 "parser.y"
    {symTab->popFrame(); (yyval.stm) = new Block((yyvsp[(3) - (4)].stml));;}
    break;

  case 183:
#line 780 "parser.y"
    {(yyval.stml) = NULL;;}
    break;

  case 184:
#line 781 "parser.y"
    {(yyval.stml) = (yyvsp[(1) - (2)].stml) ? (yyvsp[(1) - (2)].stml)->add((yyvsp[(2) - (2)].stm)) : new List<Statement>((yyvsp[(2) - (2)].stm));;}
    break;

  case 188:
#line 788 "parser.y"
    {(yyvsp[(4) - (4)].stm)->iterBound = (yyvsp[(2) - (4)].exp); (yyval.stm) = (yyvsp[(4) - (4)].stm);;}
    break;

  case 189:
#line 789 "parser.y"
    {(yyvsp[(4) - (4)].stm)->iterBound = (yyvsp[(2) - (4)].exp); (yyval.stm) = (yyvsp[(4) - (4)].stm);;}
    break;

  case 190:
#line 793 "parser.y"
    {symTab->pushFrame();;}
    break;

  case 191:
#line 795 "parser.y"
    {
      (yyval.stm) = new ForStmt((SimpleStatement*)(yyvsp[(4) - (10)].stm), (yyvsp[(6) - (10)].exp), (Assignment*)(yyvsp[(8) - (10)].stm), (yyvsp[(10) - (10)].stm));
      symTab->popFrame();
    ;}
    break;

  case 192:
#line 802 "parser.y"
    {symTab->push((VarDec*)(yyvsp[(1) - (1)].stm));;}
    break;

  case 194:
#line 807 "parser.y"
    {(yyval.stm) = new WhileStmt((yyvsp[(3) - (5)].exp), (yyvsp[(5) - (5)].stm));;}
    break;

  case 195:
#line 811 "parser.y"
    {(yyval.stm) = new DoStmt((yyvsp[(2) - (7)].stm), (yyvsp[(5) - (7)].exp));;}
    break;

  case 196:
#line 815 "parser.y"
    {(yyval.stm) = new IfStmt((yyvsp[(3) - (5)].exp), (yyvsp[(5) - (5)].stm), NULL);;}
    break;

  case 197:
#line 816 "parser.y"
    {(yyval.stm) = new IfStmt((yyvsp[(3) - (7)].exp), (yyvsp[(5) - (7)].stm), (yyvsp[(7) - (7)].stm));;}
    break;

  case 198:
#line 820 "parser.y"
    {(yyval.stm) = new SwitchStmt((yyvsp[(3) - (7)].exp), (yyvsp[(6) - (7)].cl));;}
    break;

  case 199:
#line 824 "parser.y"
    {(yyval.cl) = new List<Case>((yyvsp[(1) - (1)].c));;}
    break;

  case 200:
#line 825 "parser.y"
    {(yyval.cl) = (yyvsp[(1) - (2)].cl)->add((yyvsp[(2) - (2)].c));;}
    break;

  case 201:
#line 829 "parser.y"
    {(yyval.c) = new Case((yyvsp[(2) - (4)].exp), (yyvsp[(4) - (4)].stml));;}
    break;

  case 202:
#line 830 "parser.y"
    {(yyval.c) = new Case(NULL, (yyvsp[(3) - (3)].stml));;}
    break;

  case 204:
#line 836 "parser.y"
    {
      if ((yyvsp[(1) - (1)].exp)->exprType()->isEnumType()) {
        (yyval.exp) = (yyvsp[(1) - (1)].exp);
      }
      else {
        yyerror("case label must be an integer or an enum constant");
      }
    ;}
    break;

  case 205:
#line 850 "parser.y"
    {symTab->pushFrame();;}
    break;

  case 206:
#line 851 "parser.y"
    {(yyval.fd) = new FunDef((yyvsp[(2) - (7)].s), (yyvsp[(1) - (7)].t), (yyvsp[(5) - (7)].vdl), (Block*)(yyvsp[(7) - (7)].stm)); symTab->popFrame();;}
    break;

  case 208:
#line 856 "parser.y"
    {(yyval.vdl) = NULL;;}
    break;

  case 210:
#line 861 "parser.y"
    {(yyval.vdl) = new List<VarDec>((VarDec*)(yyvsp[(1) - (1)].stm));;}
    break;

  case 211:
#line 862 "parser.y"
    {(yyval.vdl) = (yyvsp[(1) - (3)].vdl)->add((VarDec*)(yyvsp[(3) - (3)].stm));;}
    break;

  case 212:
#line 866 "parser.y"
    {symTab->pushFrame();;}
    break;

  case 213:
#line 868 "parser.y"
    {
      (yyval.fd) = new Template((yyvsp[(7) - (11)].s), (yyvsp[(6) - (11)].t), (yyvsp[(9) - (11)].vdl), (Block*)(yyvsp[(11) - (11)].stm), (yyvsp[(4) - (11)].tdl)); symTab->popFrame();
      if (!prog.templates) {
        prog.templates = new List<Template>((Template*)(yyval.fd));
      }
      else {
        prog.templates->add((Template*)(yyval.fd));
      }
    ;}
    break;

  case 214:
#line 880 "parser.y"
    {(yyval.tdl) = NULL;;}
    break;

  case 216:
#line 885 "parser.y"
    {(yyval.tdl) = new List<TempParamDec>((TempParamDec*)(yyvsp[(1) - (1)].tpd));;}
    break;

  case 217:
#line 886 "parser.y"
    {(yyval.tdl) = (yyvsp[(1) - (3)].tdl)->add((TempParamDec*)(yyvsp[(3) - (3)].tpd));;}
    break;

  case 218:
#line 890 "parser.y"
    {(yyval.tpd) = new TempParamDec((yyvsp[(2) - (2)].s), (yyvsp[(1) - (2)].t));symTab->push((TempParamDec*)(yyval.tpd));;}
    break;


/* Line 1267 of yacc.c.  */
#line 2977 "parser.tab.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;


  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse look-ahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse look-ahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  if (yyn == YYFINAL)
    YYACCEPT;

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#ifndef yyoverflow
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEOF && yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}


#line 893 "parser.y"


#include <stdio.h>

void yyerror(const char *s) {
  fflush(stdout);
  fprintf(stderr, "%s:%d: %s\n", yyfilenm, yylineno, s);
}

