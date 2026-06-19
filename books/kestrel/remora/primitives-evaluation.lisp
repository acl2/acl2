; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable int-valuep-when-result-not-error
                          float-valuep-when-result-not-error)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ primitives-evaluation
  :parents (dynamic-semantics)
  :short "Evaluation of the Remora primitives."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Remora primitives are built-in functions
     whose definition is not written in Remora.
     Here we provide a definition of them in ACL2,
     as ACL2 functions that take and return Remora expression values.
     The functions defensively check that
     the expression values have the correct types,
     returning an error if they do not;
     the functions also return errors if
     the operation is not well-defined on the type-correct expression values
     (e.g. division by zero).")
   (xdoc::p
    "We will connect these with our formalization of @(see evaluation).
     Most likely, we will extend our ASTs with nodes for the primitives,
     similar to the Remora publications [thesis] [arxiv] [esop],
     and we will extend our evaluator to call the functions defined here
     when evaluating the application of a primitive AST.")
   (xdoc::p
    "The primitives are defined in [impl], as the Remora `prelude'.
     This is work in progress."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-value-int ((val expr-valuep))
  :returns (ival int-value-resultp)
  :short "Check if an expression value is an integer value, returning it if so."
  (b* (((unless (expr-value-case val :base)) (reserr nil))
       (bval (expr-value-base->val val))
       ((unless (base-value-case bval :int)) (reserr nil))
       (ival (base-value-int->val bval)))
    ival))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-value-float ((val expr-valuep))
  :returns (fval float-value-resultp)
  :short "Check if an expression value is a float value, returning it if so."
  (b* (((unless (expr-value-case val :base)) (reserr nil))
       (bval (expr-value-base->val val))
       ((unless (base-value-case bval :float)) (reserr nil))
       (fval (base-value-float->val bval)))
    fval))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-add ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer addition."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (+ i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-sub ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer subtraction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (- i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-mul ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer multiplication."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (* i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-div ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluaton of integer division."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (zerop i2.int)) (reserr nil)) ;; ERROR: division by zero
       (ival (int-value (floor i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-mod ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer modulo."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (zerop i2.int)) (reserr nil)) ;; ERROR: modulo zero
       (ival (int-value (mod i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-max ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer max."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (max i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-min ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer min."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (min i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-bit-and ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bit and."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logand i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-bit-or ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bit or."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logior i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-bit-xor ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bit xor."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logxor i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-shl ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer shift left."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (negp i2.int)) (reserr nil)) ;; ERROR: shift by negative bits
       (ival (int-value (ash i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-shr ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer shift right."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (negp i2.int)) (reserr nil)) ;; ERROR: shift by negative bits
       (ival (int-value (ash i1.int (- i2.int)))))
    (expr-value-base (base-value-int ival))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-bit-not ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bit not."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (ival (int-value (lognot i1.int))))
    (expr-value-base (base-value-int ival))))

; TODO: prim-int-popc
; NOTE: I think Haskell's popCount on a negative Int works by counting the
; number  of 1's in the two's complement version of the number. Since Int has a
; fixed width, the number of 1's is finite in this case. But ACL2's logcount on
; a negative integer would count the number of 1's in it's absolute
; value representation. Thus, there is a mismatch.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-eq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer equality."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (= i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-neq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer inequality."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (not (= i1.int i2.int))))
    (expr-value-base (base-value-bool bval))))

(define prim-int-lt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer less than."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (< i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-gt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer greater than."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (> i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-leq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer less than or equal."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (<= i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-geq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer greater than or equal."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (>= i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-to-float ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer conversion to float."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (fval (float-value-ratio i1.int)))
    (expr-value-base (base-value-float fval))))

(define prim-int-to-bool ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer conversion to bool."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (bval (not (zerop i1.int))))
    (expr-value-base (base-value-bool bval))))
      
