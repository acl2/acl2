; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../../../syntax/disambiguator")
(include-book "../../../syntax/parser")

(include-book "../../utilities/subst-free")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extdecl-find-fundef
  ((ident identp)
   (extdecl extdeclp))
  :returns (mv (found booleanp)
               (fundef fundefp))
  (extdecl-case
   extdecl
   :fundef (b* (((fundef fundef) extdecl.unwrap))
             (if (equal ident (declor->ident fundef.declor))
                 (mv t (c$::fundef-fix fundef))
               (mv nil (c$::irr-fundef))))
   :otherwise (mv nil (c$::irr-fundef))))

(define extdecl-list-find-fundef
  ((ident identp)
   (extdecls extdecl-listp))
  :returns (mv (erp booleanp)
               (fundef fundefp))
  (b* (((reterr) (c$::irr-fundef))
       ((when (endp extdecls))
        (reterr t))
       ((mv found fundef) (extdecl-find-fundef ident (first extdecls)))
       ((when found)
        (retok fundef)))
    (extdecl-list-find-fundef ident (rest extdecls))))

(define transunit-find-fundef
  ((ident identp)
   (transunit transunitp))
  :returns (mv (erp booleanp)
               (fundef fundefp))
  (b* (((transunit transunit) transunit))
    (extdecl-list-find-fundef ident transunit.decls)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-map ((names true-listp))
  (if (endp names)
      nil
    (cons (c$::ident (first names))
          (ident-map (rest names)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test-subst-free (input &key fun subst expected)
  `(assert-event
    (b* (((mv erp1 ast) (c$::parse-file (filepath "test")
                                        (acl2::string=>nats ,input)
                                        t))
         ((mv erp2 ast) (c$::dimb-transunit ast t))
         ((mv erp3 fundef) (transunit-find-fundef (c$::ident ,fun) ast))
         ((mv fundef$ -)
          ;; (fundef-subst-free fundef (mergesort ',subst) nil))
          (fundef-subst-free fundef ,subst nil))
         ((mv erp4 ast-expected)
          (c$::parse-file (filepath "test")
                          (acl2::string=>nats ,expected)
                          t))
         ((mv erp5 ast-expected) (c$::dimb-transunit ast-expected t))
         ((mv erp6 fundef-expected)
          (transunit-find-fundef (c$::ident ,fun) ast-expected)))
      (cond (erp1 (cw "~%PARSER ERROR: ~@0~%" erp1))
            (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2))
            (erp3 (cw "~%Could not find function: ~x0~%" ,fun))
            (erp4 (cw "~%PARSER ERROR on expected form: ~@0~%" erp4))
            (erp5 (cw "~%DISAMBIGUATOR ERROR on expected form: ~@0~%" erp5))
            (erp6 (cw "~%Could not find function in expected form: ~x0~%" ,fun))
            ((not (equal fundef$ fundef-expected))
             (cw "~%New fundef does not match the expected: ~x0~%~%" fundef))
            (t t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *42*
  (expr-const
    (c$::const-int (c$::make-iconst :core (c$::dec/oct/hex-const-dec 42)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-subst-free
  "int main(void) {
     return 0;
   }
"
  :fun "main"
  :subst nil
  :expected
  "int main(void) {
     return 0;
   }
")

(test-subst-free
  "int x, y;

   int main(void) {
     return x;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       nil)
  :expected
  "int x, y;

   int main(void) {
     return y;
   }
")

(test-subst-free
  "int b;
   int a;

   int main(void) {
     return a + b;
   }
"
  :fun "main"
  :subst (omap::update (ident "a")
                       (make-expr-ident :ident (ident "b"))
                       nil)
  :expected
  "int b;
   int a;

   int main(void) {
     return b + b;
   }
")

(test-subst-free
  "int x;

   int main(void) {
     return 0;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       nil)
  :expected
  "int x;

   int main(void) {
     return 0;
   }
")

(test-subst-free
  "int x;

   int main(void) {
     int x;
     x = 0;
     return x;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       nil)
  :expected
  "int x;

   int main(void) {
     int x;
     x = 0;
     return x;
   }
")

(test-subst-free
  "int x, y;

   int main(void) {
     x = 0;
     return x;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       nil)
  ;; Note this *does* substitute in lvalues. Thus, it is the responsibility of
  ;; the user to ensure that the range of the substitution will create valid
  ;; lvalues, or else that there are no lvalue locations which will be
  ;; substituted.
  :expected
  "int x, y;

   int main(void) {
     y = 0;
     return y;
   }
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; shadowing

(test-subst-free
  "int x, y, z;

   int main(void) {
     int x;
     return x + y;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       (omap::update (ident "y")
                                     (make-expr-ident :ident (ident "z"))
                                     nil))
  :expected
  "int x, y, z;

   int main(void) {
     int x;
     return x + z;
   }
")

(test-subst-free
  "int x, y, z;

   int main(void) {
     int x = x;
     return x + y;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       (omap::update (ident "y")
                                     (make-expr-ident :ident (ident "z"))
                                     nil))
  :expected
  "int x, y, z;

   int main(void) {
     int x = y;
     return x + z;
   }
")

(test-subst-free
  "int x, y, z;

   int main(void) {
     int y;
     int x = x;
     return x + y;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       (omap::update (ident "y")
                                     (make-expr-ident :ident (ident "z"))
                                     nil))
  :expected
  "int x, y, z;

   int main(void) {
     int y;
     int x = y;
     return x + y;
   }
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; scope blocks

(test-subst-free
  "int x, y;

   int main(void) {
     {
       int x;
     }
     return x;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       nil)
  :expected
  "int x, y;

   int main(void) {
     {
       int x;
     }
     return y;
   }
")

(test-subst-free
  "int x, y;

   int main(void) {
     {
       int x;
     }
     return 0;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "y"))
                       nil)
  :expected
  "int x, y;

   int main(void) {
     {
       int x;
     }
     return 0;
   }
")

(test-subst-free
  "int x, z;

   int main(void) {
     {
       int y = x;
     }
     return 0;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       (make-expr-ident :ident (ident "z"))
                       nil)
  :expected
  "int x, z;

   int main(void) {
     {
       int y = z;
     }
     return 0;
   }
")

(test-subst-free
  "int x;

   int main(void) {
     int y;
     if (y) {
       int z = x;
       y = z;
     }
     return y;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       nil)
  :expected
  "int x;

   int main(void) {
     int y;
     if (y) {
       int z = 42;
       y = z;
     }
     return y;
   }
")

(test-subst-free
  "int x, y;

   int main(void) {
     int y;
     for (int z = 0; z < y; z++) {
       y = x + z;
     }
     return y;
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       (omap::update (ident "y")
                                     *42*
                                     nil))
  :expected
  "int x, y;

   int main(void) {
     int y;
     for (int z = 0; z < y; z++) {
       y = 42 + z;
     }
     return y;
   }
"
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; statement expressions

(test-subst-free
  "int x;

   int main(void) {
     return ({
       int y = x;
       y;
     });
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       (omap::update (ident "y")
                                     *42*
                                     nil))
  :expected
  "int x;

   int main(void) {
     return ({
       int y = 42;
       y;
     });
   }
")

(test-subst-free
  "int x;

   int main(void) {
     return ({
       int x = 0;
       x;
     });
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       (omap::update (ident "y")
                                     *42*
                                     nil))
  :expected
  "int x;

   int main(void) {
     return ({
       int x = 0;
       x;
     });
   }
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; generic selection

(test-subst-free
  "int x;

   int main(void) {
     return _Generic((x), int: 0);
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       nil)
  :expected
  "int x;

   int main(void) {
     return _Generic((42), int: 0);
   }
")

(test-subst-free
  "int x, y, z;

   int main(void) {
     float x;
     return _Generic((x), int: y, float: z);
   }
"
  :fun "main"
  :subst (omap::update (ident "x")
                       *42*
                       (omap::update (ident "y")
                                     *42*
                                     nil))
  :expected
  "int x, y, z;

   int main(void) {
     float x;
     return _Generic((x), int: 42, float: z);
   }
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; parameters

(test-subst-free
  "int foo(int x) {
     return 0;
   }
"
  :fun "foo"
  :subst (omap::update (ident "x")
                       *42*
                       nil)
  :expected
  "int foo(int x) {
     return 0;
   }
")

(test-subst-free
  "int foo(int x) {
     return x;
   }
"
  :fun "foo"
  :subst (omap::update (ident "x")
                       *42*
                       nil)
  :expected
  "int foo(int x) {
     return x;
   }
")

(test-subst-free
  "int n;

   int foo(int args[n]) {
     return 0;
   }
"
  :fun "foo"
  :subst (omap::update (ident "n")
                       *42*
                       nil)
  :expected
  "int n;

   int foo(int args[42]) {
     return 0;
   }
")

(test-subst-free
  "int n;

   int foo(int args[n]) {
     return args[0];
   }
"
  :fun "foo"
  :subst (omap::update (ident "n")
                       *42*
                       (omap::update (ident "args")
                                     *42*
                                     nil))
  :expected
  "int n;

   int foo(int args[42]) {
     return args[0];
   }
")

(test-subst-free
  "int foo(int n, int args[n]) {
     return args[0];
   }
"
  :fun "foo"
  :subst (omap::update (ident "n")
                       *42*
                       nil)
  :expected
  "int foo(int n, int args[n]) {
     return args[0];
   }
")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; function calls

(test-subst-free
  "int foo(void);

   int bar(void) {
     foo();
     return bar();
   }
"
  :fun "bar"
  :subst (omap::update (ident "foo")
                       (make-expr-ident :ident (ident "bar"))
                       (omap::update (ident "bar")
                                     (make-expr-ident :ident (ident "foo"))
                                     nil))
  :expected
  "int foo(void);

   int bar(void) {
     bar();
     return bar();
   }
")
