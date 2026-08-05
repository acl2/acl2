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
(include-book "kestrel/arithmetic-light/expt" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define float-ratio-value ((x rationalp))
  :returns (value expr-valuep)
  (expr-value-base
   (base-value-float
    (float-value-ratio x))))

(defconst *softmax-e* 543656365691809/200000000000000)

(defconst *softmax-e-value*
  (float-ratio-value *softmax-e*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define softmax4-expt-appn ((var stringp))
  :returns (expr exprp)
  (make-expr-appn
   :fun (make-expr-var :name "f.^")
   :args (list (make-expr-var :name "e")
               (make-expr-var :name var))))

(define softmax4-add-appn ((left exprp)
                           (right exprp))
  :returns (expr exprp)
  (make-expr-appn
   :fun (make-expr-var :name "f.+")
   :args (list left right)))

(define softmax4-div-appn ((numerator exprp)
                           (denominator exprp))
  :returns (expr exprp)
  (make-expr-appn
   :fun (make-expr-var :name "f./")
   :args (list numerator denominator)))

(defconst *softmax4-denominator-expr*
  (softmax4-add-appn
   (softmax4-add-appn
    (softmax4-expt-appn "x0")
    (softmax4-expt-appn "x1"))
   (softmax4-add-appn
    (softmax4-expt-appn "x2")
    (softmax4-expt-appn "x3"))))

(define softmax4-result-expr ((var stringp))
  :returns (expr exprp)
  (softmax4-div-appn
   (softmax4-expt-appn var)
   *softmax4-denominator-expr*))

(defconst *softmax4-expr*
  (make-expr-bracket
   :exprs (list (softmax4-result-expr "x0")
                (softmax4-result-expr "x1")
                (softmax4-result-expr "x2")
                (softmax4-result-expr "x3"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define softmax4-denominator ((x0 integerp)
                              (x1 integerp)
                              (x2 integerp)
                              (x3 integerp))
  :returns (denominator rationalp)
  (+ (expt *softmax-e* x0)
     (expt *softmax-e* x1)
     (expt *softmax-e* x2)
     (expt *softmax-e* x3)))

(define softmax4 ((x0 integerp)
                  (x1 integerp)
                  (x2 integerp)
                  (x3 integerp))
  :returns (probabilities rational-listp)
  :short "Pure ACL2 specification of exact-rational four-element softmax."
  (b* ((e0 (expt *softmax-e* x0))
       (e1 (expt *softmax-e* x1))
       (e2 (expt *softmax-e* x2))
       (e3 (expt *softmax-e* x3))
       (denominator (softmax4-denominator x0 x1 x2 x3)))
    (list (/ e0 denominator)
          (/ e1 denominator)
          (/ e2 denominator)
          (/ e3 denominator))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule softmax-correct
  (implies
   (and (integerp x0)
        (integerp x1)
        (integerp x2)
        (integerp x3)
        (expr-denvp denv)
        (expr-denv-wfp denv)
        (equal (expr-denv-lookup-expr "e" denv)
               *softmax-e-value*)
        (equal (expr-denv-lookup-expr "x0" denv)
               (float-ratio-value x0))
        (equal (expr-denv-lookup-expr "x1" denv)
               (float-ratio-value x1))
        (equal (expr-denv-lookup-expr "x2" denv)
               (float-ratio-value x2))
        (equal (expr-denv-lookup-expr "x3" denv)
               (float-ratio-value x3))
        (equal (expr-denv-lookup-expr "f.+" denv)
               (expr-value-primop
                (primop-value-float-binary
                 (float-binary-primop-add))))
        (equal (expr-denv-lookup-expr "f.^" denv)
               (expr-value-primop
                (primop-value-float-binary
                 (float-binary-primop-expt))))
        (equal (expr-denv-lookup-expr "f./" denv)
               (expr-value-primop
                (primop-value-float-binary
                 (float-binary-primop-div))))
        (equal softmax4-result (softmax4 x0 x1 x2 x3))
        (integerp limit)
        (>= limit 100))
   (equal
    (eval-expr *softmax4-expr* denv limit)
    (expr-value-vector
     (list (float-ratio-value (car softmax4-result))
           (float-ratio-value (cadr softmax4-result))
           (float-ratio-value (caddr softmax4-result))
           (float-ratio-value (cadddr softmax4-result))))))
  :enable (eval-expr-when-var
           eval-expr-when-appn
           eval-expr-list-when-atom
           eval-expr-list-when-consp
           eval-expr-when-bracket
           eval-app-of-float-add-no-lifting
           eval-app-of-float-expt-no-lifting
           eval-app-of-float-div-no-lifting
           expr-value-wfp-when-base
           dims-of-expr-value-when-base
           dims-of-expr-value-when-primop
           list-repeatp
           float-ratio-value
           softmax4
           softmax4-denominator))
