; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "../constant-expressions")
(include-book "../disambiguator")
(include-book "../parser")
(include-book "../validator")

(include-book "std/strings/cat" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *constant-expressions-test-c17-dialect*
  (c::make-dialect :std (c::standard-c17)))

(defconst *constant-expressions-test-gcc-c17-dialect*
  (c::make-dialect :std (c::standard-c17) :gcc t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Wrap the input expression with a declaration of x and a function definition.
;; This gives x a meaning and provides a valid context in which to disambiguate
;; and validate the expression, adding the annotations needed by the ICE check.
(defmacro test-ice (input expected &key dialect)
  `(assert-event
    (b* ((dialect (or ,dialect
                       *constant-expressions-test-c17-dialect*))
         (ienv (change-ienv (ienv-default) :dialect dialect))
         (filepath (filepath "test"))
         (source (str::cat "int x;
void f(void) {
  " ,input ";
}
"))
         (fileset
          (fileset
           (omap::update filepath
                         (filedata (acl2::string=>nats source))
                         nil)))
         ((mv erp1 ast) (parse-fileset fileset dialect t nil))
         ((when erp1) (cw "~%PARSER ERROR: ~@0~%" erp1))
         ((mv erp2 ast) (dimb-trans-ensemble ast ienv nil))
         ((when erp2) (cw "~%DISAMBIGUATOR ERROR: ~@0~%" erp2))
         ((mv erp3 ast) (valid-trans-ensemble ast ienv nil))
         ((when erp3) (cw "~%VALIDATOR ERROR: ~@0~%" erp3))
         (tunit (omap::head-val (trans-ensemble->units ast)))
         (item (second (trans-unit->items tunit)))
         (edecl (trans-item-declon->declon item))
         (fundef (ext-declon-fundef->fundef edecl))
         (block-item (first (comp-stmt->items (fundef->body fundef))))
         (stmt (block-item-stmt->stmt block-item))
         (expr (stmt-expr->expr? stmt)))
      (equal (expr-ice-p expr t dialect) ,expected))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic operands.

(test-ice "1" t)

(test-ice "x" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cast restrictions.

(test-ice "(double) 1" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expression operands of sizeof.

(test-ice "sizeof(x)" nil)

(test-ice "sizeof((double) 1)" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Target type names of casts.

(test-ice "sizeof((int (*)[x]) 1)" nil)

(test-ice "sizeof((int (*)[(int) (double) 1]) 1)" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type-name operands of sizeof.

(test-ice "sizeof(int (*)[x])" nil)

;; The casts are exempted, but the bound may be evaluated, and this checker
;; does not establish the representability of the conversions.
(test-ice "sizeof(int (*)[(int) (double) 1])" :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Standard type-name operands of alignof.

(test-ice "_Alignof(int (*)[x])" nil)

;; Unlike the sizeof case above, the alignof operand is definitely unevaluated.
(test-ice "_Alignof(int (*)[(int) (double) 1])" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; GCC expression operands of alignof.

(test-ice "__alignof__(x)"
          nil
          :dialect *constant-expressions-test-gcc-c17-dialect*)

(test-ice "__alignof__(1)"
          :unknown
          :dialect *constant-expressions-test-gcc-c17-dialect*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Operands of typeof.

(test-ice "sizeof(typeof(x))"
          nil
          :dialect *constant-expressions-test-gcc-c17-dialect*)

(test-ice "sizeof(typeof(int (*)[x]))"
          nil
          :dialect *constant-expressions-test-gcc-c17-dialect*)
