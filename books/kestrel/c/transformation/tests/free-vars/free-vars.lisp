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

(include-book "../../utilities/free-vars")

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

(defmacro test-free-vars (input &key fun vars)
  `(assert-event
    (b* (((mv erp1 ast) (c$::parse-file (filepath "test")
                                        (acl2::string=>nats ,input)
                                        t))
         ((mv erp2 ast) (c$::dimb-transunit ast t))
         ((mv erp3 fundef) (transunit-find-fundef (c$::ident ,fun) ast))
         (free-vars (free-vars-fundef fundef nil))
         (expected (mergesort (ident-map (list ,@vars)))))
      (cond (erp1 (cw "~%PARSER ERROR: ~@0~%" erp1))
            (erp2 (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2))
            (erp3 (cw "~%Could not find function: ~x0~%" ,fun))
            ((not (equal free-vars expected))
             (cw "~%Free variables: ~x0~%Expected: ~x1~%" free-vars expected))
            (t t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(test-free-vars
  "int main(void) {
     return 0;
   }
"
  :fun "main"
  :vars ())

(test-free-vars
  "int x;

   int main(void) {
     return x;
   }
"
  :fun "main"
  :vars ("x"))

(test-free-vars
  "int b;
   int a;

   int main(void) {
     return a + b;
   }
"
  :fun "main"
  :vars ("b" "a"))

(test-free-vars
  "int x;

   int main(void) {
     return 0;
   }
"
  :fun "main"
  :vars ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; shadowing

(test-free-vars
  "int x, y;

   int main(void) {
     int x;
     return x + y;
   }
"
  :fun "main"
  :vars ("y"))

(test-free-vars
  "int x, y;

   int main(void) {
     int x = x;
     return x + y;
   }
"
  :fun "main"
  :vars ("x" "y"))

(test-free-vars
  "int x, y;

   int main(void) {
     int y;
     int x = x;
     return x + y;
   }
"
  :fun "main"
  :vars ("x"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; scope blocks

(test-free-vars
  "int x;

   int main(void) {
     {
       int x;
     }
     return x;
   }
"
  :fun "main"
  :vars ("x"))

(test-free-vars
  "int x;

   int main(void) {
     {
       int x;
     }
     return 0;
   }
"
  :fun "main"
  :vars ())

(test-free-vars
  "int x;

   int main(void) {
     {
       int y = x;
     }
     return 0;
   }
"
  :fun "main"
  :vars ("x"))

(test-free-vars
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
  :vars ("x"))

(test-free-vars
  "int x;

   int main(void) {
     int y;
     for (int z = 0; z < y; z++) {
       y = x + z;
     }
     return y;
   }
"
  :fun "main"
  :vars ("x"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; statement expressions

(test-free-vars
  "int x;

   int main(void) {
     return ({
       int y = x;
       y;
     });
   }
"
  :fun "main"
  :vars ("x"))

(test-free-vars
  "int x;

   int main(void) {
     return ({
       int x = 0;
       x;
     });
   }
"
  :fun "main"
  :vars ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; generic selection

(test-free-vars
  "int x;

   int main(void) {
     return _Generic((x), int: 0);
   }
"
  :fun "main"
  :vars ("x"))

(test-free-vars
  "int x, y, z;

   int main(void) {
     float x;
     return _Generic((x), int: y, float: z);
   }
"
  :fun "main"
  :vars ("y" "z"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; parameters

(test-free-vars
  "int foo(int x) {
     return 0;
   }
"
  :fun "foo"
  :vars ())

(test-free-vars
  "int foo(int x) {
     return x;
   }
"
  :fun "foo"
  :vars ())

(test-free-vars
  "int n;

   int foo(int args[n]) {
     return 0;
   }
"
  :fun "foo"
  :vars ("n"))

(test-free-vars
  "int n;

   int foo(int args[n]) {
     return args[0];
   }
"
  :fun "foo"
  :vars ("n"))

(test-free-vars
  "int foo(int n, int args[n]) {
     return args[0];
   }
"
  :fun "foo"
  :vars ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; function calls

(test-free-vars
  "int foo(void);

   int bar(void) {
     foo();
     return bar();
   }
"
  :fun "bar"
  :vars ("foo"))
