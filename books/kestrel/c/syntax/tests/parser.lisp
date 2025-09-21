; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../parser")

(include-book "std/testing/assert-bang-stobj" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Test parsing functions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-parse (fn input &key pos more-inputs gcc cond)
  ;; INPUT is an ACL2 term with the text to parse,
  ;; where the term evaluates to a string.
  ;; Optional POS is the initial position for the parser state.
  ;; Optional MORE-INPUTS go just before parser state input.
  ;; GCC flag says whether GCC extensions are enabled.
  ;; Optional COND may be over variables AST, SPAN, PARSTATE
  ;; and also EOF-POS for PARSE-EXTERNAL-DECLARATION-LIST.
  `(assert!-stobj
    (b* ((parstate (init-parstate (acl2::string=>nats ,input) ,gcc parstate))
         (,(if (eq fn 'parse-external-declaration-list)
               '(mv erp ?ast ?span ?eofpos parstate)
             '(mv erp ?ast ?span parstate))
          (,fn ,@more-inputs parstate))
         ,@(and pos
                `((parstate (update-parstate->position ,pos parstate)))))
      (mv (if erp
              (cw "~@0" erp) ; CW returns NIL, so ASSERT!-STOBJ fails
            ,(or cond t)) ; assertion passes if COND is absent or else holds
          parstate))
    parstate))

(defmacro test-parse-fail (fn input &key pos more-inputs gcc)
  ;; INPUT is an ACL2 term with the text to parse,
  ;; where the term evaluates to a string.
  ;; Optional POS is the initial position for the parser state.
  ;; Optional MORE-INPUTS go just before parser state input.
  ;; GCC flag says whether GCC extensions are enabled.
  `(assert!-stobj
    (b* ((parstate (init-parstate (acl2::string=>nats ,input) ,gcc parstate))
         (,(if (eq fn 'parse-external-declaration-list)
               '(mv erp ?ast ?span ?eofpos parstate)
             '(mv erp ?ast ?span parstate))
          (,fn ,@more-inputs parstate))
         ,@(and pos
                `((parstate (update-parstate->position ,pos parstate)))))
      (mv erp parstate))
    parstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-cast-expression

(test-parse
 parse-cast-expression
 "0xFFFF"
 :cond (expr-case ast :const))

(test-parse
 parse-cast-expression
 "(uint32_t) x"
 :cond (expr-case ast :cast))

(test-parse
 parse-cast-expression
 "(T) (x)"
 :cond (expr-case ast :cast/call-ambig))

(test-parse
 parse-cast-expression
 "(T) * x"
 :cond (expr-case ast :cast/mul-ambig))

(test-parse
 parse-cast-expression
 "(T) + x"
 :cond (expr-case ast :cast/add-ambig))

(test-parse
 parse-cast-expression
 "(T) - x"
 :cond (expr-case ast :cast/sub-ambig))

(test-parse
 parse-cast-expression
 "(T) & x"
 :cond (expr-case ast :cast/and-ambig))

(test-parse
 parse-cast-expression
 "(A(B)) ++ (C) [3]"
 :cond (and (expr-case ast :cast/call-ambig)
            (equal (expr-cast/call-ambig->inc/dec ast)
                   (list (inc/dec-op-inc)))))

(test-parse
 parse-cast-expression
 "(( __be16)(__u16)f());"
 :cond (and (expr-case ast :paren)
            (expr-case (expr-paren->inner ast) :cast)
            (expr-case (expr-cast->arg (expr-paren->inner ast)) :cast)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-unary-expression

(test-parse
 parse-unary-expression
 "123")

(test-parse
 parse-unary-expression
 "sizeof y"
 :cond (expr-case ast :unary))

(test-parse
 parse-unary-expression
 "sizeof (x+y)"
 :cond (expr-case ast :unary))

(test-parse
 parse-unary-expression
 "sizeof (_Atomic(int))"
 :cond (expr-case ast :sizeof))

(test-parse
 parse-unary-expression
 "sizeof (var_or_tydef)"
 :cond (expr-case ast :sizeof-ambig))

(test-parse
 parse-unary-expression
 "sizeof(also(ambig))"
 :cond (expr-case ast :sizeof-ambig))

(test-parse
 parse-unary-expression
 "sizeof(x).m"
 :cond (and (expr-case ast :unary)
            (expr-case (expr-unary->arg ast) :member)))

(test-parse
 parse-unary-expression
 "sizeof(x)->m"
 :cond (and (expr-case ast :unary)
            (expr-case (expr-unary->arg ast) :memberp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-postfix-expression

(test-parse
 parse-postfix-expression
 "var"
 :cond (expr-case ast :ident))

(test-parse
 parse-postfix-expression
 "var[4]"
 :cond (expr-case ast :arrsub))

(test-parse
 parse-postfix-expression
 "var[4].a->u(y,w)[q+e]"
 :cond (and (expr-case ast :arrsub)
            (expr-case (expr-arrsub->arg1 ast) :funcall)
            (expr-case (expr-arrsub->arg2 ast) :binary)))

(test-parse
 parse-postfix-expression
 "(int[]) { 1, 2, 3, }")

(test-parse
 parse-postfix-expression
 "(int) {}.x"
 :gcc t
 :cond (expr-case ast :member))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-expression

(test-parse
 parse-expression
 "f(x+1,3)")

(test-parse
 parse-expression
 "__builtin_types_compatible_p(typeof(a), signed long long)"
 :gcc t)

(test-parse
 parse-expression
 "__builtin_offsetof(struct pt_regs, ss)"
 :gcc t)

(test-parse
 parse-expression
 "__builtin_va_arg(args, ngx_str_t *)"
 :gcc t)

(test-parse
 parse-expression
 "({x = 0;})(x)"
 :cond (expr-case ast :funcall)
 :gcc t)

(test-parse
 parse-expression
 "sizeof(*ctx)"
 :cond (and (expr-case ast :unary)
            (expr-case (expr-unary->arg ast) :paren)))

(test-parse
 parse-expression
 "__extension__ x"
 :gcc t)

(test-parse
 parse-expression
 "__extension__ x + y"
 :gcc t)

(test-parse
 parse-expression
 "__extension__ (x + y)"
 :gcc t)

(test-parse
 parse-expression
 "((int) {}.x)"
 :gcc t
 :cond (and (expr-case ast :paren)
            (expr-case (expr-paren->inner ast) :member)))

(test-parse
 parse-expression
 "sizeof ((struct s) {}.x)"
 :gcc t
 :cond (expr-case ast :unary))

(test-parse
 parse-expression
 "((struct s) {}.x)"
 :gcc t
 :cond (and (expr-case ast :paren)
            (expr-case (expr-paren->inner ast) :member)))

(test-parse
 parse-expression
 "(struct s) {}.x"
 :gcc t
 :cond (expr-case ast :member))

(test-parse
 parse-expression
 "((struct s) {})"
 :gcc t
 :cond (and (expr-case ast :paren)
            (expr-case (expr-paren->inner ast) :complit)))

(test-parse
 parse-expression
 "(id) {}.x)"
 :gcc t
 :cond (expr-case ast :member))

(test-parse
 parse-expression
 "((id) {}.x))"
 :gcc t
 :cond (and (expr-case ast :paren)
            (expr-case (expr-paren->inner ast) :member)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-designator

(test-parse
 parse-designator
 "[18]")

(test-parse
 parse-designator
 "[0 ... 9]"
 :gcc t)

(test-parse-fail
 parse-designator
 "[0 ... 9]")

(test-parse
 parse-designator
 ".m")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-struct-or-union-specifier

(test-parse
 parse-struct-or-union-specifier
 "empty {}"
 :pos (position 1 7)
 :more-inputs (t (span (position 1 0) (position 1 6)))
 :gcc t
 :cond (type-spec-case ast :struct-empty))

(test-parse
 parse-struct-or-union-specifier
 "{}"
 :pos (position 1 7)
 :more-inputs (t (span (position 1 0) (position 1 6)))
 :gcc t
 :cond (type-spec-case ast :struct-empty))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-array/function-abstract-declarator

(test-parse
 parse-array/function-abstract-declarator
 "[]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[const]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[const _Atomic]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[*uu]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[*]"
 :cond (dirabsdeclor-case ast :array-star))

(test-parse
 parse-array/function-abstract-declarator
 "[80]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[restrict 80+0]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-array/function-abstract-declarator
 "[static restrict 80+0]"
 :cond (dirabsdeclor-case ast :array-static1))

(test-parse
 parse-array/function-abstract-declarator
 "[restrict static 80+0]"
 :cond (dirabsdeclor-case ast :array-static2))

(test-parse
 parse-array/function-abstract-declarator
 "(id)"
 :cond (dirabsdeclor-case ast :function))

(test-parse
 parse-array/function-abstract-declarator
 "(int x, int y)"
 :cond (dirabsdeclor-case ast :function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-direct-abstract-declarator

(test-parse
 parse-direct-abstract-declarator
 "(*)"
 :cond (dirabsdeclor-case ast :paren))

(test-parse
 parse-direct-abstract-declarator
 "(*)[]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-direct-abstract-declarator
 "(*)[const _Atomic]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-direct-abstract-declarator
 "(*)[80]"
 :cond (dirabsdeclor-case ast :array))

(test-parse
 parse-direct-abstract-declarator
 "(*)[80](int x, int y)"
 :cond (dirabsdeclor-case ast :function))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-direct-declarator

(test-parse
 parse-direct-declarator
 "x"
 :cond (dirdeclor-case ast :ident))

(test-parse
 parse-direct-declarator
 "(x)"
 :cond (dirdeclor-case ast :paren))

(test-parse
 parse-direct-declarator
 "x[]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[10]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[a+b]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[const a+b]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[const volatile a+b]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[static a+b]"
 :cond (dirdeclor-case ast :array-static1))

(test-parse
 parse-direct-declarator
 "x[static const a+b]"
 :cond (dirdeclor-case ast :array-static1))

(test-parse
 parse-direct-declarator
 "x[const static a+b]"
 :cond (dirdeclor-case ast :array-static2))

(test-parse
 parse-direct-declarator
 "x[*]"
 :cond (dirdeclor-case ast :array-star))

(test-parse
 parse-direct-declarator
 "x[*y]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[restrict *]"
 :cond (dirdeclor-case ast :array-star))

(test-parse
 parse-direct-declarator
 "x[restrict *y]"
 :cond (dirdeclor-case ast :array))

(test-parse
 parse-direct-declarator
 "x[_Atomic static *y]"
 :cond (dirdeclor-case ast :array-static2))

(test-parse
 parse-direct-declarator
 "(a)(b)"
 :cond (dirdeclor-case ast :function-params))

(test-parse
 parse-direct-declarator
 "f(int, _Bool)"
 :cond (dirdeclor-case ast :function-params))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-abstract-declarator

(test-parse
 parse-abstract-declarator
 "[a[3]]"
 :cond (and (equal (absdeclor->pointers ast) nil)
            (dirabsdeclor-case (absdeclor->direct? ast) :array)))

(test-parse
 parse-abstract-declarator
 "(a)"
 :cond (and (equal (absdeclor->pointers ast) nil)
            (dirabsdeclor-case (absdeclor->direct? ast) :function)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-declarator

(test-parse
 parse-declarator
 "o")

(test-parse
 parse-declarator
 "*o")

(test-parse
 parse-declarator
 "*o[15]")

(test-parse
 parse-declarator
 "(*o)[15]")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-parameter-declaration

(test-parse
 parse-parameter-declaration
 "int x,"
 :cond (param-declor-case (param-declon->declor ast) :nonabstract))

(test-parse
 parse-parameter-declaration
 "int *x,"
 :cond (param-declor-case (param-declon->declor ast) :nonabstract))

(test-parse
 parse-parameter-declaration
 "int *,"
 :cond (param-declor-case (param-declon->declor ast) :abstract))

(test-parse
 parse-parameter-declaration
 "int (x)(y))"
 :cond (param-declor-case (param-declon->declor ast) :ambig))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-declarator-or-abstract-declarator

(test-parse
 parse-declarator-or-abstract-declarator
 "zzz,"
 :cond (amb?-declor/absdeclor-case ast :declor))

(test-parse
 parse-declarator-or-abstract-declarator
 "(*),"
 :cond (amb?-declor/absdeclor-case ast :absdeclor))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h),"
 :cond (amb?-declor/absdeclor-case ast :ambig))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h)[*],"
 :cond (amb?-declor/absdeclor-case ast :ambig))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h)[*](uint32_t),"
 :cond (amb?-declor/absdeclor-case ast :ambig))

(test-parse
 parse-declarator-or-abstract-declarator
 "(h)[*](uint32_t)(T,T),"
 :cond (amb?-declor/absdeclor-case ast :ambig))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-expression-or-type-name

(test-parse
 parse-expression-or-type-name
 "abc)"
 :more-inputs (t)
 :cond (amb?-expr/tyname-case ast :ambig))

(test-parse
 parse-expression-or-type-name
 "id(id))"
 :more-inputs (nil)
 :cond (amb?-expr/tyname-case ast :ambig))

(test-parse
 parse-expression-or-type-name
 "+x)"
 :more-inputs (t)
 :cond (amb?-expr/tyname-case ast :expr))

(test-parse
 parse-expression-or-type-name
 "int *)"
 :more-inputs (nil)
 :cond (amb?-expr/tyname-case ast :tyname))

(test-parse
 parse-expression-or-type-name
 "a + b)"
 :more-inputs (t)
 :cond (amb?-expr/tyname-case ast :expr))

(test-parse
 parse-expression-or-type-name
 "a _Atomic)"
 :more-inputs (nil)
 :cond (amb?-expr/tyname-case ast :tyname))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-declaration

(test-parse
 parse-declaration
 "extern int remove (const char *__filename)
    __attribute__ ((__nothrow__ , __leaf__));"
 :gcc t)

(test-parse
 parse-declaration
 "int __seg_fs *x;"
 :gcc t)

(test-parse
 parse-declaration
 "int __seg_gs *x;"
 :gcc t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-statement

(test-parse
 parse-statement
 "   printf(\"exploit_read_from_file(): \"
          \"bytes_read=%zd is supposed to be bytes_expected_to_be_read=%zd, \"
          \"pre_offset=%ld is supposed to be post_offset=%ld, \"
          \"pre_offset is supposed to be 1, \"
          \"post_offset is supposed to be 1.\\n\",
          ret, exploit_size,
          pre_offset, post_offset);")

(test-parse
 parse-statement
 "return (*(const volatile typeof( _Generic((*(unsigned long *)addr), char: (char)0, unsigned char: (unsigned char)0, signed char: (signed char)0, unsigned short: (unsigned short)0, signed short: (signed short)0, unsigned int: (unsigned int)0, signed int: (signed int)0, unsigned long: (unsigned long)0, signed long: (signed long)0, unsigned long long: (unsigned long long)0, signed long long: (signed long long)0, default: (*(unsigned long *)addr))) *)&(*(unsigned long *)addr));"
 :gcc t)

(test-parse
 parse-statement
 "case 'a' ... 'z': return;"
 :gcc t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-block-item

(test-parse
 parse-block-item
 "idx = &((char*)session_peak())[i*BUFSIZE];")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-external-declaration

(test-parse
 parse-external-declaration
 ";"
 :cond (extdecl-case ast :empty)
 :gcc t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; parse-external-declaration-list

(test-parse
 parse-external-declaration-list
 "struct mystruct
{
   int *val;
};")

(test-parse
 parse-external-declaration-list
 "typedef void foo;
struct bar
{
 int val;
};")

(test-parse
 parse-external-declaration-list
 "int ith(int *a) {
 return a[0];
}")

(test-parse
 parse-external-declaration-list
 "int ith(int a[]) {
 return a[0];
}")

(test-parse
 parse-external-declaration-list
 "void foo (int val) {
 printf(\"Val = %d\\n\", val);
}")

(test-parse
 parse-external-declaration-list
 "int main() { }")

(test-parse
 parse-external-declaration-list
 "int foo (unsigned int v)
{
 return (v >> 1);
}")

(test-parse
 parse-external-declaration-list
 "void encrypt (uint32_t* v) {
}")

(test-parse
 parse-external-declaration-list
 "void encrypt () {
  uint32_t v0=1;
}")

(test-parse
 parse-external-declaration-list
 "void foo () {
  gen_config_t gen_config = {100};
}")

(test-parse
 parse-external-declaration-list
 "int A [] = {0,1,2,3};")

(test-parse
 parse-external-declaration-list
 "int spec_int(unsigned int v)
{
  unsigned int c;
  for (c = 0; v; v >>= 1)
    c += v & 1;
  return c;
}")

(test-parse
 parse-external-declaration-list
 "int sum(int a[], int n) {
  int s = 0;
  for (int i = 1; i <= n; ++i)
    s += a[i];
  return s;
}")

(test-parse
 parse-external-declaration-list
 "int foo (char x, char y) { return x < y && y < x; }")

(test-parse
 parse-external-declaration-list
 "int foo (int x, int y) { return x < y || y < x; }")

(test-parse
 parse-external-declaration-list
 "int foo (int x) { int z = 0 ; z &= x; }")

(test-parse
 parse-external-declaration-list
 "void foo () {
  while (x > y) {
    x++;
  }
}")

(test-parse
 parse-external-declaration-list
 "int foo () {
  int i = 0;
  i--;
}")

(test-parse
 parse-external-declaration-list
 "int main() {
 int a = 10, b = 5;
 a %= b;
}")

(test-parse
 parse-external-declaration-list
 "char string[] = \"\";")

(test-parse
 parse-external-declaration-list
 "void foo () {
  managedtask * newtask = (managedtask *) malloc(sizeof(managedtask));
}")

(test-parse
 parse-external-declaration-list
 "void foo () {
 idx = (arr)[3];
}")

(test-parse
 parse-external-declaration-list
 "void test(int i)
{
    y[i] = (i ? inv : src)[i];
}")

(test-parse
 parse-external-declaration-list
 "extern char *tmpnam (char[20]);")

(test-parse
 parse-external-declaration-list
 "extern int __uflow (FILE *);")

(test-parse
 parse-external-declaration-list
 "int c[1][2];")

(test-parse
 parse-external-declaration-list
 "struct A
{
  int c1, c2;
};")

(test-parse
 parse-external-declaration-list
 "long long foo () {
  return 1LL;
}")

(test-parse
 parse-external-declaration-list
 "extern int sscanf (const char *__s, const char *__format, ...);")

(test-parse
 parse-external-declaration-list
 "extern int remove (const char *__filename) __attribute__ ((__nothrow__ , __leaf__));"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "typedef int register_t __attribute__ ((__mode__ (__word__)));"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "extern int fscanf (FILE *__restrict __stream, const char *__restrict __format, ...) __asm__ (\"\" \"__isoc99_fscanf\") ;"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "void foo() {
  for (size_t bar; ; ) {}
}")

(test-parse
 parse-external-declaration-list
 "static int func_1(void)
{
   int i;
lbl_15:
   return 2;
}")

(test-parse
 parse-external-declaration-list
 "extern __inline __attribute__ ((__always_inline__)) __attribute__ ((__gnu_inline__)) void
error (int __status, int __errnum, const char *__format, ...)
{
 if (__builtin_constant_p (__status) && __status != 0)
   __error_noreturn (__status, __errnum, __format, __builtin_va_arg_pack ());
 else
   __error_alias (__status, __errnum, __format, __builtin_va_arg_pack ());
}"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "int foo asm (\"myfoo\") = 2;"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "extern struct static_call_key __SCK__might_resched; extern typeof(__cond_resched) __SCT__might_resched;;"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "static ngx_thread_value_t __stdcall ngx_iocp_timer(void *data);"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "__declspec(thread) int nevents = 0;"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "__declspec(thread) WSAEVENT events[WSA_MAXIMUM_WAIT_EVENTS + 1];"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "__declspec(thread) ngx_connection_t *conn[WSA_MAXIMUM_WAIT_EVENTS + 1];"
 :gcc t)

(test-parse
 parse-block-item-list
 "__asm__ (
        \"cpuid\"
    : \"=a\" (eax), \"=b\" (ebx), \"=c\" (ecx), \"=d\" (edx) : \"a\" (i) );
  buf[0] = eax;
  }"
 :gcc t
 :cond (equal (len ast) 2))

(test-parse
 parse-external-declaration-list
 "const void *x = 0;
  // foo
  void *y = (void *) x;
  // bar
")

(test-parse
 parse-external-declaration-list
 "void * foo(void) {
  const void *x = 0;
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored \"-Wcast-qual\"
  return (void *) x;
#pragma GCC diagnostic pop
}
")

(test-parse-fail
 parse-external-declaration-list
 "void * foo(void) {
  const #pragma GCC diagnostic push
    void *x = 0;
#pragma GCC diagnostic ignored \"-Wcast-qual\"
  return (void *) x;
#pragma GCC diagnostic pop
}
")

(test-parse
 parse-external-declaration-list
 "#pragma once
  int x;
")

(test-parse
 parse-external-declaration-list
 " #pragma once
  int x;
")

(test-parse
 parse-external-declaration-list
 "#pragma once
  int x;
")

(test-parse
 parse-external-declaration-list
 "#pragma onceint x;
"
 :cond (equal (len ast) 1))

(test-parse
 parse-external-declaration-list
 "int foo (int arg __attribute__((unused))) {
  return 0;
}
"
 :gcc t)

(test-parse
 parse-external-declaration-list
 "struct s x = {};
"
 :gcc t)
