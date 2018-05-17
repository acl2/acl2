%option yylineno

%s ACTIVE

Rac (rac|RAC|)
lineba ^"#"\ [0-9]+\ \"[^\"]*\".*\n
%{
#include <stdio.h>
extern int yylex();
#include "parser.h"
#include "parser.tab.h"
extern void yyerror(const char *);
static void comment();
char* tokstr();
static void lineba();
char yyfilenm[1024];
%}

%%

{lineba}                    {lineba();}

[ ]*\/\/\ *{Rac}\:?\ *begin\ *\n  {BEGIN ACTIVE;}
\/\/\ *{Rac}\:?\ *end\ *\n        {BEGIN INITIAL;}

<INITIAL>.*\n               {}

"/*"                        {comment();}
\/\/{Rac}\:?.*             {yyless(7); return RAC;}
\/\/\ {Rac}\:?.*           {yyless(8); return RAC;}
"//".*                      {}
"Hector::".*                {}
"#pragma".*                 {}
[ \n\t]                     {}
.*print.*                   {}

"typedef"                   {return TYPEDEF;}
"template"                  {return TEMPLATE;}
"struct"                    {return STRUCT;}
"enum"                      {return ENUM;}
"const"                     {return CONST;}
"int"	                    {return INT;}
"uint"	                    {return UINT;}
"int64"	                    {return INT64;}
"uint64"	            {return UINT64;}
"bool"	                    {return BOOL;}
"wait"	                    {return WAIT;}
"for"	                    {return FOR;}
"if"	                    {return IF;}
"else"	                    {return ELSE;}
"while"	                    {return WHILE;}
"do"	                    {return DO;}
"switch"	            {return SWITCH;}
"case"	                    {return CASE;}
"default"                   {return DEFAULT;}
"break"	                    {return BREAK;}
"continue"                  {return CONTINUE;}
"return"                    {return RETURN;}
"assert"                    {return ASSERT;}
"to_uint"                   {return TO_UINT;}
"to_uint64"                 {return TO_UINT64;}
"range"                     {return RANGE;}
"slc"                       {return SLC;}
"set_slc"                   {return SET_SLC;}

"tuple"                     {return TUPLE;}
"array"                     {return ARRAY;}
"tie"                       {return TIE;}

"sc_int"                    {return SC_INT;}
"sc_bigint"                 {return SC_BIGINT;}
"sc_fixed"                  {return SC_FIXED;}
"sc_uint"                   {return SC_UINT;}
"sc_biguint"                {return SC_BIGUINT;}
"sc_ufixed"                 {return SC_UFIXED;}

"ac_int"                    {return AC_INT;}

"true"                      {yylval.s = tokstr(); return TRUE;}
"false"                     {yylval.s = tokstr(); return FALSE;}

[a-zA-Z_][a-zA-Z_0-9]*      {yylval.s = tokstr(); return (prog.typeDefs->find(yytext)) ? TYPEID : (prog.templates->find(yytext)) ? TEMPLATEID : ID;}

[0-9]+ |
"0x"[a-fA-F_0-9]+           {yylval.s = tokstr(); return NAT;}

">>="			    {yylval.s = tokstr(); return RSHFT_ASSIGN;}
"<<="			    {yylval.s = tokstr(); return LSHFT_ASSIGN;}
"+="			    {yylval.s = tokstr(); return ADD_ASSIGN;}
"-="			    {yylval.s = tokstr(); return SUB_ASSIGN;}
"*="			    {yylval.s = tokstr(); return MUL_ASSIGN;}
"%="			    {yylval.s = tokstr(); return MOD_ASSIGN;}
"&="			    {yylval.s = tokstr(); return AND_ASSIGN;}
"^="			    {yylval.s = tokstr(); return XOR_ASSIGN;}
"|="			    {yylval.s = tokstr(); return OR_ASSIGN;}

"++"			    {yylval.s = tokstr(); return INC_OP;}
"--"			    {yylval.s = tokstr(); return DEC_OP;}

">>"			    {yylval.s = tokstr(); return RSHFT_OP;}
"<<"			    {yylval.s = tokstr(); return LSHFT_OP;}

"&&"			    {yylval.s = tokstr(); return AND_OP;}
"||"			    {yylval.s = tokstr(); return OR_OP;}
"<="			    {yylval.s = tokstr(); return LE_OP;}
">="			    {yylval.s = tokstr(); return GE_OP;}
"=="			    {yylval.s = tokstr(); return EQ_OP;}
"!="			    {yylval.s = tokstr(); return NE_OP;}

"=" |
"+" |
"-" |
"&" |
"!" |
"~" |
"*" |
"/" |
"%" |
"<" |
">" |
"|" |
"^"                        {yylval.s = tokstr(); return yytext[0];}

"(" |
")" |
"{" |
"}" |
"[" |
"]" |
"," |
";" |
":" |
"." |
"?"                         {return yytext[0];}

%%

static void comment() {
  int c;
  while ((c = yyinput()) != 0) {
    if (c == '*') {
      while ((c = yyinput()) == '*') {}
      if (c == '/') return;
      if (c == 0) break;
    }
  }
  yyerror("unterminated comment");
}

char* tokstr() {
  char *str = new char[yyleng+1];
  strcpy(str, yytext);
  return str;
}

int yywrap(void) {  // called at end of input
  return 1;
}

static void lineba() {
  char *i = strtok(yytext, "# \"");
  char *f = strtok(NULL, "# \"");
  sscanf(i, "%d", &yylineno);
  sscanf(f, "%s", yyfilenm);
}
