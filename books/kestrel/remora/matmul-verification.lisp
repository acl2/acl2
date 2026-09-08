; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "evaluation-rules")
(include-book "workshops/2003/hendrix/support/mmult" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This file verifies that a ACL2 Remora program computing 2x2 matrix
;;; multiplication is correct.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-ratio-value ((x rationalp))
  :returns (value expr-valuep)
  (expr-value-base
   (base-value-float
    (float-value-ratio x))))

(define float-ratio-value-list ((xs rational-listp))
  :returns (values expr-value-listp)
  (if (endp xs)
      nil
    (cons (float-ratio-value (car xs))
          (float-ratio-value-list (cdr xs)))))

(define float-ratio-vector-value ((xs rational-listp))
  :returns (value expr-valuep)
  (expr-value-vector (float-ratio-value-list xs)))

(define rational-matrixp (x)
  :returns (yes/no booleanp)
  (if (consp x)
      (and (rational-listp (car x))
           (rational-matrixp (cdr x)))
    (null x)))

(define float-ratio-vector-value-list ((rows rational-matrixp))
  :returns (values expr-value-listp)
  :guard-hints (("Goal" :in-theory (enable rational-matrixp)))
  (if (endp rows)
      nil
    (cons (float-ratio-vector-value (car rows))
          (float-ratio-vector-value-list (cdr rows)))))

(define float-ratio-matrix-value ((rows rational-matrixp))
  :returns (value expr-valuep)
  (expr-value-vector (float-ratio-vector-value-list rows)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define matmul-var-expr ((name stringp))
  :returns (expr exprp)
  (make-expr-var :name name))

(define matmul-mul-appn ((left exprp) (right exprp))
  :returns (expr exprp)
  (make-expr-appn
   :fun (make-expr-var :name "f.*")
   :args (list left right)))

(define matmul-add-appn ((left exprp) (right exprp))
  :returns (expr exprp)
  (make-expr-appn
   :fun (make-expr-var :name "f.+")
   :args (list left right)))

;; One entry of the product: a*b + c*d, on variables.
(define matmul-entry-expr ((a stringp) (b stringp) (c stringp) (d stringp))
  :returns (expr exprp)
  (matmul-add-appn
   (matmul-mul-appn (matmul-var-expr a) (matmul-var-expr b))
   (matmul-mul-appn (matmul-var-expr c) (matmul-var-expr d))))

(defconst *matmul2x2-expr*
  (make-expr-bracket
   :exprs
   (list (make-expr-bracket
          :exprs (list (matmul-entry-expr "a00" "b00" "a01" "b10")
                       (matmul-entry-expr "a00" "b01" "a01" "b11")))
         (make-expr-bracket
          :exprs (list (matmul-entry-expr "a10" "b00" "a11" "b10")
                       (matmul-entry-expr "a10" "b01" "a11" "b11"))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule matmul-correct
  (implies
   (and (rationalp a00) (rationalp a01) (rationalp a10) (rationalp a11)
        (rationalp b00) (rationalp b01) (rationalp b10) (rationalp b11)
        (<= 0 a00) (<= 0 a01) (<= 0 a10) (<= 0 a11)
        (<= 0 b00) (<= 0 b01) (<= 0 b10) (<= 0 b11)
        (expr-denvp denv)
        (expr-denv-wfp denv)
        (equal (expr-denv-lookup-expr "a00" denv) (float-ratio-value a00))
        (equal (expr-denv-lookup-expr "a01" denv) (float-ratio-value a01))
        (equal (expr-denv-lookup-expr "a10" denv) (float-ratio-value a10))
        (equal (expr-denv-lookup-expr "a11" denv) (float-ratio-value a11))
        (equal (expr-denv-lookup-expr "b00" denv) (float-ratio-value b00))
        (equal (expr-denv-lookup-expr "b01" denv) (float-ratio-value b01))
        (equal (expr-denv-lookup-expr "b10" denv) (float-ratio-value b10))
        (equal (expr-denv-lookup-expr "b11" denv) (float-ratio-value b11))
        (equal (expr-denv-lookup-expr "f.+" denv)
               (expr-value-primop
                (primop-value-float-binary
                 (float-binary-primop-add))))
        (equal (expr-denv-lookup-expr "f.*" denv)
               (expr-value-primop
                (primop-value-float-binary
                 (float-binary-primop-mul))))
        (equal matmul-result
               (acl2::m* (list (list a00 a01) (list a10 a11))
                         (list (list b00 b01) (list b10 b11))))
        (integerp limit)
        (>= limit 100))
   (equal (eval-expr *matmul2x2-expr* denv limit)
          (float-ratio-matrix-value matmul-result)))
  :enable (eval-expr-when-var
           eval-expr-when-appn
           eval-expr-list-when-atom
           eval-expr-list-when-consp
           eval-expr-when-bracket
           eval-app-of-float-add-no-lifting
           eval-app-of-float-mul-no-lifting
           expr-value-wfp-when-base
           expr-value-wfp
           check-dims-of-expr-value
           check-dims-of-expr-value-list
           dims-of-expr-value
           dims-of-expr-value-when-base
           dims-of-expr-value-when-primop
           list-repeatp
           float-ratio-value
           float-ratio-value-list
           float-ratio-vector-value
           float-ratio-vector-value-list
           float-ratio-matrix-value
           acl2::m*
           acl2::col*
           acl2::dot*
           acl2::m-emptyp
           acl2::row-car
           acl2::row-cdr
           acl2::row-cons
           acl2::col-car
           acl2::col-cdr))
