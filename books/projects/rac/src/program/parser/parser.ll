%option yylineno
%option nounput

%s ACTIVE

Rac (rac|RAC|Rac)
lineba ^"#"\ [0-9]+\ \"[^\"]*\".*\n

%{
#include "yyparser.h"
#include "parser.tab.hpp"

#include <stdio.h>

static bool comment();
char *tokstr();
static void lineba();

#define YY_USER_ACTION {                                                      \
  yylloc.last_line = yylineno;                                                \
  yylloc.first_line = yylloc.last_line;                                       \
  yylloc.first_column = yylloc.last_column;                                   \
  yylloc.f_pos = yylloc.f_pos_end;                                            \
  yylloc.f_pos_end += yyleng;                                                 \
  for(int i = 0; yytext[i] != '\0'; i++) {                                    \
    if(yytext[i] == '\n') {                                                   \
      yylloc.last_line++;                                                     \
      yylloc.last_column = 0;                                                 \
    }                                                                         \
    else {                                                                    \
      yylloc.last_column++;                                                   \
    }                                                                         \
  }                                                                           \
}

%}
%%


{lineba}                    {lineba();}

[ ]*\/\/\ *{Rac}\:?\ *begin\ *\n  {BEGIN ACTIVE;}
\/\/\ *{Rac}\:?\ *end\ *\n        {BEGIN INITIAL;}

<INITIAL>.*\n               {}

"/*"                        { if (!comment()) return 1; }
"//".*                      {}
"#pragma".*                 {}
[ \n\t]                     {}

"typedef"                   {return TYPEDEF;}
"template"                  {return TEMPLATE;}
"struct"                    {return STRUCT;}
"enum"                      {return ENUM;}
"const"                     {return CONST;}
"static"                    {return STATIC;}
"int"                       {return INT;}
"uint"                      {return UINT;}
"int64"                     {return INT64;}
"uint64"                    {return UINT64;}
"bool"                      {return BOOL;}
"for"                       {return FOR;}
"if"                        {return IF;}
"else"                      {return ELSE;}
"while"                     {return WHILE;}
"do"                        {return DO;}
"switch"                    {return SWITCH;}
"case"                      {return CASE;}
"default"                   {return DEFAULT;}
"break"                     {return BREAK;}
"return"                    {return RETURN;}
"__RAC_ASSERT"              {return ASSERT;}
"assert"                    {return ASSERT;}
"slc"                       {return SLC;}
"set_slc"                   {return SET_SLC;}

"tuple"                     {return TUPLE;}
"array"                     {return ARRAY;}
"tie"                       {return TIE;}

"ac_int"                    {return AC_INT;}
"ac_fixed"                  {return AC_FIXED;}

"true"                      {yylval.s = tokstr(); return TRUE;}
"false"                     {yylval.s = tokstr(); return FALSE;}

[a-zA-Z_][a-zA-Z_0-9]*      {yylval.s = tokstr();
                             if (yyast.getType(yytext)) {
                               return TYPEID;
                             } else if (yyast.getTemplate(yytext)) {
                               return TEMPLATEID;
                             } else {
                               return ID;
                             }
                            }


[0-9]+(("u"|"U")?("ll"|"LL")?|("ll"|"LL")?("u"|"U")) |
"0b"[0-1]+(("u"|"U")?("ll"|"LL")?|("ll"|"LL")?("u"|"U")) |
"0x"[a-fA-F_0-9]+(("u"|"U")?("ll"|"LL")?|("ll"|"LL")?("u"|"U")) {yylval.s = tokstr(); return NAT;}

">>="            {yylval.s = tokstr(); return RSHFT_ASSIGN;}
"<<="            {yylval.s = tokstr(); return LSHFT_ASSIGN;}
"+="             {yylval.s = tokstr(); return ADD_ASSIGN;}
"-="             {yylval.s = tokstr(); return SUB_ASSIGN;}
"*="             {yylval.s = tokstr(); return MUL_ASSIGN;}
"/="             {yylval.s = tokstr(); return DIV_ASSIGN;}
"%="             {yylval.s = tokstr(); return MOD_ASSIGN;}
"&="             {yylval.s = tokstr(); return AND_ASSIGN;}
"^="             {yylval.s = tokstr(); return XOR_ASSIGN;}
"|="             {yylval.s = tokstr(); return OR_ASSIGN;}

"++"             {yylval.s = tokstr(); return INC_OP;}
"--"             {yylval.s = tokstr(); return DEC_OP;}

">>"             {yylval.s = tokstr(); return RSHFT_OP;}
"<<"             {yylval.s = tokstr(); return LSHFT_OP;}

"&&"             {yylval.s = tokstr(); return AND_OP;}
"||"             {yylval.s = tokstr(); return OR_OP;}
"<="             {yylval.s = tokstr(); return LE_OP;}
">="             {yylval.s = tokstr(); return GE_OP;}
"=="             {yylval.s = tokstr(); return EQ_OP;}
"!="             {yylval.s = tokstr(); return NE_OP;}

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
"^"              {yylval.s = tokstr(); return yytext[0];}

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
"?"              {return yytext[0];}

%%

static bool
comment ()
{
  int c = yyinput();
  yylloc.f_pos_end += 1;

  while (c != '\0')
    {
      if (c == '*')
        {
          c = yyinput();
          yylloc.f_pos_end += 1;
          if (c == '/')
            return true;
        }
      else {
        c = yyinput();
        yylloc.f_pos_end += 1;
      }
    }
  yyast.diag().new_error(yylloc, "Unterminated comment").report();
  return false;
}

char *
tokstr ()
{
  return strndup(yytext, yyleng);
}

int
yywrap (void)
{ // called at end of input
  return 1;
}

static void
lineba ()
{
  char *cur = nullptr;

  char *i = strtok_r(yytext, "# \"", &cur);
  yylineno = atoi(i);

  char *f = strtok_r(nullptr, "# \"", &cur);
  yylloc.file_name = std::string(f);
}
