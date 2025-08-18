; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../disambiguator")
(include-book "../parser")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-dimb (input &key gcc cond)
  ;; INPUT is an ACL2 string with the text to parse and disambiguate.
  ;; GCC flag says whether GCC extensions are enabled.
  ;; Optional COND may be over variable AST.
  `(assert-event
    (b* (((mv erp1 ast) (parse-file (filepath "test")
                                    (acl2::string=>nats ,input)
                                    ,gcc))
         (- (cw "~%Input:~%~x0~|" ast))
         ((mv erp2 ast) (dimb-transunit ast ,gcc)))
      (cond (erp1 (cw "~%PARSER ERROR: ~@0" erp1))
            (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0" erp2))
            (t (and ,(or cond t)
                    (prog2$ (cw "~%Output:~%~x0~|" ast) t)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-dimb
 "int x;
")

(test-dimb
 "enum {a, b, c};
  int x = b;
")

(test-dimb
 "int main(void) {
    return 0;
  }
")

(test-dimb
 "void f();
")

(test-dimb
 "void f() {}
")

(test-dimb
 "int x;
  void f() {
  int y = sizeof(x);
  }
")

(test-dimb
 "typedef char x;
  void f() {
  int y = sizeof(x);
  }
")

(test-dimb
 "int x;
  void f(x) {}
")

(test-dimb
 "typedef char x;
  void f(x);
")

(test-dimb
 "void f(int(x));
")

(test-dimb
 "typedef char x;
  void f(int(x));
")

(test-dimb
 "void f(int *(x));
")

(test-dimb
 "typedef char x;
  void f(int *(x));
")

(test-dimb
 "int a;
  void f() {
  int b;
  a * b;
  }
")

(test-dimb
 "typedef _Bool a;
  void f() {
  int b;
  a * b;
  }
")

(test-dimb
 "void f() {
  int a(int);
  int b;
  int amb = (a)(b);
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)(b);
  }
")

(test-dimb
 "void f() {
  int a(int);
  int b;
  int amb = (a)--++--++(b);
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)--++--++(b);
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int amb = (a)*b;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)*b;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int amb = (a)+b;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int amb = (a)+b;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)+b*c;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)+b*c;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)&b;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)&b;
  }
")

(test-dimb
 "void f() {
  int a;
  int b;
  int c;
  int amb = (a)&b+c;
  }
")

(test-dimb
 "void f() {
  typedef int a;
  int b;
  int c;
  int amb = (a)&b+c;
  }
")

(test-dimb
 "unsigned int size_t;
  void foo() {
  for (size_t; ; ) {}
  }
")

(test-dimb
 "typedef unsigned int size_t;
  void foo() {
  for (size_t; ; ) {}
  }
")

(test-dimb
 "int myarray[];
  int foo () {
  int x = sizeof(myarray);
  }
")

(test-dimb
 "int foo (int *a, int *b) {
 return (char *) (a) - b;
}
"
 :cond (b* ((edecls (transunit->decls ast))
            (edecl (car edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (stmt (fundef->body fundef))
            (items (stmt-compound->items stmt))
            (item (car items))
            (stmt (block-item-stmt->stmt item))
            (expr (stmt-return->expr? stmt)))
         (and (expr-case expr :binary)
              (binop-case (expr-binary->op expr) :sub))))

(test-dimb
 "int foo (int a, int b, int c) {
 return a + (b) + c;
}
"
 :cond (b* ((edecls (transunit->decls ast))
            (edecl (car edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (stmt (fundef->body fundef))
            (items (stmt-compound->items stmt))
            (item (car items))
            (stmt (block-item-stmt->stmt item))
            (expr-abc (stmt-return->expr? stmt))
            (expr-ab (expr-binary->arg1 expr-abc))
            (expr-a (expr-binary->arg1 expr-ab))
            (expr-bp (expr-binary->arg2 expr-ab))
            (expr-b (expr-paren->inner expr-bp))
            (expr-c (expr-binary->arg2 expr-abc)))
         (and (expr-case expr-abc :binary)
              (expr-case expr-ab :binary)
              (expr-case expr-a :ident)
              (expr-case expr-bp :paren)
              (expr-case expr-b :ident)
              (expr-case expr-c :ident)
              (equal (expr-ident->ident expr-a)
                     (ident "a"))
              (equal (expr-ident->ident expr-b)
                     (ident "b"))
              (equal (expr-ident->ident expr-c)
                     (ident "c")))))

(test-dimb
 "int foo (int a, int b, int c) {
  return (a) + (b) + c;
}
"
 :cond (b* ((edecls (transunit->decls ast))
            (edecl (car edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (stmt (fundef->body fundef))
            (items (stmt-compound->items stmt))
            (item (car items))
            (stmt (block-item-stmt->stmt item))
            (expr-abc (stmt-return->expr? stmt))
            (expr-ab (expr-binary->arg1 expr-abc))
            (expr-ap (expr-binary->arg1 expr-ab))
            (expr-a (expr-paren->inner expr-ap))
            (expr-bp (expr-binary->arg2 expr-ab))
            (expr-b (expr-paren->inner expr-bp))
            (expr-c (expr-binary->arg2 expr-abc)))
         (and (expr-case expr-abc :binary)
              (expr-case expr-ab :binary)
              (expr-case expr-ap :paren)
              (expr-case expr-a :ident)
              (expr-case expr-bp :paren)
              (expr-case expr-b :ident)
              (expr-case expr-c :ident)
              (equal (expr-ident->ident expr-a)
                     (ident "a"))
              (equal (expr-ident->ident expr-b)
                     (ident "b"))
              (equal (expr-ident->ident expr-c)
                     (ident "c")))))

(test-dimb
 "int foo (int a, int b, int c, int d) {
  return a + (b) + (c) + d;
}
"
 :cond (b* ((edecls (transunit->decls ast))
            (edecl (car edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (stmt (fundef->body fundef))
            (items (stmt-compound->items stmt))
            (item (car items))
            (stmt (block-item-stmt->stmt item))
            (expr-abcd (stmt-return->expr? stmt))
            (expr-abc (expr-binary->arg1 expr-abcd))
            (expr-ab (expr-binary->arg1 expr-abc))
            (expr-a (expr-binary->arg1 expr-ab))
            (expr-bp (expr-binary->arg2 expr-ab))
            (expr-b (expr-paren->inner expr-bp))
            (expr-cp (expr-binary->arg2 expr-abc))
            (expr-c (expr-paren->inner expr-cp))
            (expr-d (expr-binary->arg2 expr-abcd)))
         (and (expr-case expr-abcd :binary)
              (expr-case expr-abc :binary)
              (expr-case expr-ab :binary)
              (expr-case expr-a :ident)
              (expr-case expr-bp :paren)
              (expr-case expr-b :ident)
              (expr-case expr-cp :paren)
              (expr-case expr-c :ident)
              (expr-case expr-d :ident)
              (equal (expr-ident->ident expr-a)
                     (ident "a"))
              (equal (expr-ident->ident expr-b)
                     (ident "b"))
              (equal (expr-ident->ident expr-c)
                     (ident "c"))
              (equal (expr-ident->ident expr-d)
                     (ident "d")))))

(test-dimb
 "int foo (int a, int b) {
  return ~ (a) + b;
}
"
 :cond (b* ((edecls (transunit->decls ast))
            (edecl (car edecls))
            (fundef (extdecl-fundef->unwrap edecl))
            (stmt (fundef->body fundef))
            (items (stmt-compound->items stmt))
            (item (car items))
            (stmt (block-item-stmt->stmt item))
            (expr (stmt-return->expr? stmt)))
         (expr-case expr :binary)))
