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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Whether sizeof has an integer-constant result, based on its operand type.

(assert-event
  (equal (type-sizeof-result-const-3p (type-sint))
         t))

(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-array
             :of (type-sint)
             :kind (make-type-array-kind-const-len :len 10)))
         t))

;; An unknown constant length does not make the array a VLA.
(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-array
             :of (type-sint)
             :kind (make-type-array-kind-const-len :len nil)))
         t))

(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-array
             :of (type-sint)
             :kind (type-array-kind-nonconst-len)))
         nil))

(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-array
             :of (type-sint)
             :kind (type-array-kind-unknown-complete)))
         :unknown))

(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-array
             :of (type-sint)
             :kind (type-array-kind-incomplete)))
         :unknown))

;; A constant outer bound does not hide a variable-length element type.
(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-array
             :of (make-type-array
                   :of (type-sint)
                   :kind (type-array-kind-nonconst-len))
             :kind (make-type-array-kind-const-len :len 10)))
         nil))

;; The pointed-to type does not affect whether sizeof the pointer is constant.
(assert-event
  (equal (type-sizeof-result-const-3p
           (make-type-pointer
             :to (make-type-array
                   :of (type-sint)
                   :kind (type-array-kind-nonconst-len))))
         t))

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
      (equal (expr-ice-p expr dialect) ,expected))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Basic operands.

(test-ice "1" t)

;; An object identifier is not an allowed C17 ICE operand.
(test-ice "x" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Rejected expressions.

;; A floating constant is only allowed as an immediate cast operand.
(test-ice "1.0" nil)

;; An evaluated assignment is prohibited in a constant expression.
(test-ice "x = 1" nil)

;; An evaluated increment is prohibited in a constant expression.
(test-ice "x++" nil)

;; An evaluated comma operator is prohibited in a constant expression.
(test-ice "1, 2" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cases requiring value evaluation.

;; Unary minus is not evaluated to establish representability.
(test-ice "-1" :unknown)

;; Addition is not evaluated to establish representability.
(test-ice "1 + 2" :unknown)

;; Division is not evaluated to detect division by zero.
(test-ice "1 / 0" :unknown)

;; The cast is not evaluated to establish representability.
(test-ice "(int) 1.0" :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Cast restrictions.

;; The cast target is not an integer type.
(test-ice "(double) 1" nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Expression operands of sizeof.

;; The unevaluated identifier is still not an allowed ICE operand.
(test-ice "sizeof(x)" nil)

(test-ice "sizeof((double) 1)" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Target type names of casts.

;; The cast target's array bound contains the disallowed identifier x.
(test-ice "sizeof((int (*)[x]) 1)" nil)

(test-ice "sizeof((int (*)[(int) (double) 1]) 1)" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Type-name operands of sizeof.

;; The operand type's array bound contains the disallowed identifier x.
(test-ice "sizeof(int (*)[x])" nil)

;; The possibly evaluated casts have unknown representability.
(test-ice "sizeof(int (*)[(int) (double) 1])" :unknown)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Standard type-name operands of alignof.

;; The operand type's array bound contains the disallowed identifier x.
(test-ice "_Alignof(int (*)[x])" nil)

;; Unlike the sizeof case above, the alignof operand is definitely unevaluated.
(test-ice "_Alignof(int (*)[(int) (double) 1])" t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; GCC expression operands of alignof.

;; The expression operand contains the disallowed identifier x.
(test-ice "__alignof__(x)"
          nil
          :dialect *constant-expressions-test-gcc-c17-dialect*)

;; The expression-operand extension has unknown ICE status.
(test-ice "__alignof__(1)"
          :unknown
          :dialect *constant-expressions-test-gcc-c17-dialect*)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Operands of typeof.

;; The typeof operand contains the disallowed identifier x.
(test-ice "sizeof(typeof(x))"
          nil
          :dialect *constant-expressions-test-gcc-c17-dialect*)

;; The nested type's array bound contains the disallowed identifier x.
(test-ice "sizeof(typeof(int (*)[x]))"
          nil
          :dialect *constant-expressions-test-gcc-c17-dialect*)
