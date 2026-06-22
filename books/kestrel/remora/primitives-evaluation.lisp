; Remora Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Quan Luu (quan.luu@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "REMORA")

(include-book "values")

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

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
  :short "Evaluation of integer division."
  :long "<p>Integer division uses ACL2's @(tsee floor), which rounds towards
  minus infinity. This is consistent with [impl], which uses Haskell's
  @('div')</p>"
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (= i2.int 0)) (reserr nil)) ;; ERROR: division by zero
       (ival (int-value (floor i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-mod ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer modulo."
  :long "<p>Integer modulo uses ACL2's @(tsee mod), whose result takes the sign
  of the divisor. This is consistent with [impl], which uses Haskell's
  @('mod')</p>"
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (= i2.int 0)) (reserr nil)) ;; ERROR: modulo zero
       (ival (int-value (mod i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-max ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer maximum."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (max i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-min ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer minimum."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (min i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-bit-and ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise conjunction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logand i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-bit-or ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise inclusive disjunction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logior i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-bit-xor ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise exclusive disjunction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logxor i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-shl ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer left shift."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (< i2.int 0)) (reserr nil)) ;; ERROR: shift by negative bits
       (ival (int-value (ash i1.int i2.int))))
    (expr-value-base (base-value-int ival))))

(define prim-int-shr ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer right shift."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (< i2.int 0)) (reserr nil)) ;; ERROR: shift by negative bits
       (ival (int-value (ash i1.int (- i2.int)))))
    (expr-value-base (base-value-int ival))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-bit-not ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise negation."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (ival (int-value (lognot i1.int))))
    (expr-value-base (base-value-int ival))))

; TODO: prim-int-popc
; NOTE: Haskell's popCount on a negative Int works by counting the
; number  of 1's in the two's complement version of the number. Since Int has a
; fixed width, the number of 1's is finite in this case. But ACL2's logcount on
; a negative integer would count the number of 1's in it's absolute
; value representation. Thus, there is a mismatch. We currently resolved this
; by only accepting positive integers and errs on a negative input.
(define prim-int-popc ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer pop count."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((when (< i1.int 0)) (reserr nil)) ;; ERROR: negative input
       (ival (int-value (logcount i1.int))))
    (expr-value-base (base-value-int ival))))

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
  :short "Evaluation of integer less-than comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (< i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-gt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer greater-than comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (> i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-leq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer less-than-or-equal-to comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (<= i1.int i2.int)))
    (expr-value-base (base-value-bool bval))))

(define prim-int-geq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer greater-than-or-equal-to comparison."
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
  :short "Evaluation of integer conversion to boolean."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (bval (not (= i1.int 0))))
    (expr-value-base (base-value-bool bval))))
