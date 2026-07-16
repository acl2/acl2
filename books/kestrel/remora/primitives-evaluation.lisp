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

(include-book "expression-values-and-environments")

(include-book "kestrel/fty/boolean-result" :dir :system)

(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/abs" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (enable int-valuep-when-result-not-error
                          float-valuep-when-result-not-error
                          booleanp-when-result-not-error)))

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
     This is work in progress.")
   (xdoc::p
    "The integer primitives currently implemented are:")
   (xdoc::ul
    (xdoc::li "@(tsee prim-int-add), @(tsee prim-int-sub),
               @(tsee prim-int-mul), @(tsee prim-int-div),
               @(tsee prim-int-expt), @(tsee prim-int-mod),
               @(tsee prim-int-max), @(tsee prim-int-min).")
    (xdoc::li "@(tsee prim-int-bit-and), @(tsee prim-int-bit-or),
               @(tsee prim-int-bit-xor), @(tsee prim-int-bit-not),
               @(tsee prim-int-shl), @(tsee prim-int-shr),
               @(tsee prim-int-popc).")
    (xdoc::li "@(tsee prim-int-eq), @(tsee prim-int-neq),
               @(tsee prim-int-lt), @(tsee prim-int-gt),
               @(tsee prim-int-leq), @(tsee prim-int-geq).")
    (xdoc::li "@(tsee prim-int-to-float), @(tsee prim-int-to-bool)."))
   (xdoc::p
    "The boolean primitives currently implemented are
     @(tsee prim-bool-not), @(tsee prim-bool-and), @(tsee prim-bool-or),
     @(tsee prim-bool-eq), @(tsee prim-bool-neq),
     @(tsee prim-bool-to-int), and @(tsee prim-bool-to-float).")
   (xdoc::p
    "The float primitives currently implemented are:")
   (xdoc::ul
    (xdoc::li "@(tsee prim-float-add), @(tsee prim-float-sub),
               @(tsee prim-float-mul), @(tsee prim-float-div),
               @(tsee prim-float-expt), @(tsee prim-float-max),
               @(tsee prim-float-min), @(tsee prim-float-sqrt).")
    (xdoc::li "@(tsee prim-float-eq), @(tsee prim-float-neq),
               @(tsee prim-float-lt), @(tsee prim-float-gt),
               @(tsee prim-float-leq), @(tsee prim-float-geq).")
    (xdoc::li "@(tsee prim-float-truncate), @(tsee prim-float-round),
               @(tsee prim-float-ceiling), @(tsee prim-float-floor)."))
   (xdoc::p
    "The polymorphic primitives currently implemented are
     @(tsee prim-head), @(tsee prim-tail), @(tsee prim-length),
     @(tsee prim-append), and @(tsee prim-reverse).")
   (xdoc::p
    "For integers, we currently model Remora integer values as unbounded
     mathematical integers, matching ACL2's own integer type.
     This keeps the integer primitives easy to define for now;
     once Remora settles on a specific integer model
     (e.g. a fixed-width type such as 64-bit integers),
     the definitions can be updated accordingly.
     Two consequences of the unbounded model are worth noting,
     where our behavior differs from [impl]
     (which uses Haskell's fixed-width @('Int')):")
   (xdoc::ul
    (xdoc::li "Arithmetic never overflows. In particular, the left shift
               @(tsee prim-int-shl) never discards high-order bits, whereas a
               bounded model would wrap around or truncate.")
    (xdoc::li "Pop count @(tsee prim-int-popc) only accepts non-negative
               inputs, erroring on negative ones, because the bit count of a
               negative integer depends on a fixed two's-complement width,
               which the unbounded model lacks."))
   (xdoc::p
    "For floats, we similarly model Remora float values as unbounded
     ACL2 rationals, together with the special values negative zero, positive
     and negative infinity, and NaN (see @(tsee float-value)).
     Finite arithmetic is performed as exact rational arithmetic, and the
     results of the special cases (those involving NaN, the infinities, or
     negative zero) follow [impl]'s Haskell semantics.
     As with integers, this is a starting point for testing until Remora
     decides on a specific float model.")
   (xdoc::p
    "The boolean primitives need no special modeling:
     Remora boolean values are ACL2 booleans directly."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-expr-value-bool ((val expr-valuep))
  :returns (bval boolean-resultp)
  :short "Check if an expression value is a boolean value, returning it if so."
  (b* (((unless (expr-value-case val :base)) (reserr nil))
       (bval (expr-value-base->val val))
       ((unless (base-value-case bval :bool)) (reserr nil))
       (b (base-value-bool->val bval)))
    b))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-add ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer addition."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (+ i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-add
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-sub ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer subtraction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (- i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-sub
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-mul ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer multiplication."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (* i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-mul
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-div ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer division."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer division uses ACL2's @(tsee floor),
     which rounds towards minus infinity.
     This is consistent with [impl],
     which uses Haskell's @('div')."))
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (= i2.int 0)) (reserr nil)) ;; ERROR: division by zero
       (ival (int-value (floor i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-div
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-expt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer exponentiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "A negative exponent is an error.
     This is consistent with [impl],
     which uses Haskell's @('^')."))
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (< i2.int 0)) (reserr nil)) ;; ERROR: negative exponent
       (ival (int-value (expt i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-expt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-mod ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer modulo."
  :long
  (xdoc::topstring
   (xdoc::p
    "Integer modulo uses ACL2's @(tsee mod),
     whose result takes the sign of the divisor.
     This is consistent with [impl],
     which uses Haskell's @('mod')."))
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (= i2.int 0)) (reserr nil)) ;; ERROR: modulo zero
       (ival (int-value (mod i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-mod
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-max ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer maximum."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (max i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-max
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-min ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer minimum."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (min i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-min
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-bit-and ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise conjunction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logand i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-bit-and
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-bit-or ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise inclusive disjunction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logior i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-bit-or
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-bit-xor ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise exclusive disjunction."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (ival (int-value (logxor i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-bit-xor
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-shl ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer left shift."
  :long
  (xdoc::topstring
   (xdoc::p
    "Left shift uses ACL2's @(tsee ash)
     with a non-negative shift amount,
     erroring on a negative shift amount.
     Because integers are modeled as unbounded
     (see @(see primitives-evaluation)),
     the shift never overflows:
     no high-order bits are lost.
     This differs from [impl],
     which uses Haskell's fixed-width @('shiftL'),
     where bits shifted past the word width are discarded."))
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (< i2.int 0)) (reserr nil)) ;; ERROR: shift by negative bits
       (ival (int-value (ash i1.int i2.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-shl
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-shr ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer right shift."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       ((when (< i2.int 0)) (reserr nil)) ;; ERROR: shift by negative bits
       (ival (int-value (ash i1.int (- i2.int)))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-shr
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-bit-not ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer bitwise negation."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (ival (int-value (lognot i1.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-bit-not
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-popc ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer pop count."
  :long
  (xdoc::topstring
   (xdoc::p
    "Pop count (the number of set bits) uses ACL2's @(tsee logcount).
     Only non-negative inputs are accepted;
     a negative input is an error.
     On a negative integer,
     [impl]'s Haskell @('popCount') counts the set bits
     of the fixed-width two's-complement representation
     (a finite, width-dependent count),
     whereas @(tsee logcount) counts the bits of the unbounded magnitude.
     Because integers are modeled as unbounded
     (see @(see primitives-evaluation)),
     there is no fixed width to match,
     so the behavior on negative inputs would differ from [impl];
     we therefore restrict to non-negative inputs for now."))
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((when (< i1.int 0)) (reserr nil)) ;; ERROR: negative input
       (ival (int-value (logcount i1.int))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-int-popc
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-eq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer equality."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (= i1.int i2.int)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-eq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-neq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer inequality."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (not (= i1.int i2.int))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-neq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-lt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer less-than comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (< i1.int i2.int)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-lt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-gt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer greater-than comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (> i1.int i2.int)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-gt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-leq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer less-than-or-equal-to comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (<= i1.int i2.int)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-leq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-geq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer greater-than-or-equal-to comparison."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       ((ok (int-value i2)) (check-expr-value-int val2))
       (bval (>= i1.int i2.int)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-geq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-int-to-float ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer conversion to float."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (fval (float-value-ratio i1.int)))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-int-to-float
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-int-to-bool ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer conversion to boolean."
  (b* (((ok (int-value i1)) (check-expr-value-int val1))
       (bval (not (= i1.int 0))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-int-to-bool
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-float-add ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float addition."
  :long
  (xdoc::topstring
   (xdoc::p
    "Finite values are added as exact rationals
     (see @(see primitives-evaluation) for the float model).
     The special cases follow [impl]:")
   (xdoc::ul
    (xdoc::li
     "NaN + anything = NaN.")
    (xdoc::li
     "(+inf) + (-inf) = NaN.")
    (xdoc::li
     "(+inf) + @('x') = +inf, where @('x') is a finite rational.")
    (xdoc::li
     "(-inf) + @('x') = -inf, where @('x') is a finite rational.")
    (xdoc::li
     "(-0) + (-0) = -0; every other sum that is zero is +0.")))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (nan1 (float-value-case f1 :nan))
       (nan2 (float-value-case f2 :nan))
       (pinf1 (float-value-case f1 :posinf))
       (pinf2 (float-value-case f2 :posinf))
       (ninf1 (float-value-case f1 :neginf))
       (ninf2 (float-value-case f2 :neginf))
       (n0-1 (float-value-case f1 :neg0))
       (n0-2 (float-value-case f2 :neg0))
       (fval
        (cond
          ;; 1. NaN + anything = NaN
          ((or nan1 nan2) (float-value-nan))
          ;; 2. +inf + -inf = NaN
          ((or (and pinf1 ninf2) (and ninf1 pinf2)) (float-value-nan))
          ;; 3. +inf + anything else = +inf
          ((or pinf1 pinf2) (float-value-posinf))
          ;; 4. -inf + anything else = -inf
          ((or ninf1 ninf2) (float-value-neginf))
          ;; 5. -0 + -0 = -0
          ((and n0-1 n0-2) (float-value-neg0))
          ;; 6. standard rational addition with -0 = 0
          (t (b* ((r1 (if n0-1
                          0
                        (float-value-ratio->ratio f1)))
                  (r2 (if n0-2
                          0
                        (float-value-ratio->ratio f2))))
               (float-value-ratio (+ r1 r2)))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-add
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-sub ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float subtraction."
  :long
  (xdoc::topstring
   (xdoc::p
    "Finite values are subtracted as exact rationals
     (see @(see primitives-evaluation) for the float model).
     The special cases follow [impl]:")
   (xdoc::ul
    (xdoc::li
     "NaN - anything = NaN; anything - NaN = NaN.")
    (xdoc::li
     "(+inf) - (+inf) = NaN; (-inf) - (-inf) = NaN.")
    (xdoc::li
     "(+inf) - @('x') = +inf; @('x') - (-inf) = +inf,
      where @('x') is a finite rational.")
    (xdoc::li
     "(-inf) - @('x') = -inf; @('x') - (+inf) = -inf,
      where @('x') is a finite rational.")
    (xdoc::li
     "(-0) - (+0) = -0; every other difference that is zero is +0.")))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (nan1 (float-value-case f1 :nan))
       (nan2 (float-value-case f2 :nan))
       (pinf1 (float-value-case f1 :posinf))
       (pinf2 (float-value-case f2 :posinf))
       (ninf1 (float-value-case f1 :neginf))
       (ninf2 (float-value-case f2 :neginf))
       (n0-1 (float-value-case f1 :neg0))
       (n0-2 (float-value-case f2 :neg0))
       (fval
        (cond
          ;; 1. NaN - anything = NaN and anything - NaN = NaN
          ((or nan1 nan2) (float-value-nan))
          ;; 2. +inf - +inf = NaN and -inf - -inf = NaN
          ((or (and pinf1 pinf2) (and ninf1 ninf2)) (float-value-nan))
          ;; 3. +inf - anything else = +inf and anything else - -inf = +inf
          ((or pinf1 ninf2) (float-value-posinf))
          ;; 4. -inf - anything else = -inf and anything else - +inf = -inf
          ((or ninf1 pinf2) (float-value-neginf))
          ;; 5. -0 - 0 = -0
          ((and n0-1
                (float-value-case f2 :ratio)
                (= (float-value-ratio->ratio f2) 0))
           (float-value-neg0))
          ;; 6. standard rational addition with -0 = 0
          (t (b* ((r1 (if n0-1
                          0
                        (float-value-ratio->ratio f1)))
                  (r2 (if n0-2
                          0
                        (float-value-ratio->ratio f2))))
               (float-value-ratio (- r1 r2)))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-sub
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-mul ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float multiplication."
  :long
  (xdoc::topstring
   (xdoc::p
    "Finite values are multiplied as exact rationals
     (see @(see primitives-evaluation) for the float model).
     The sign of an infinite or zero result is
     the exclusive-or of the operand signs
     (negative zero counts as negative).
     The special cases follow [impl]:")
   (xdoc::ul
    (xdoc::li
     "NaN * anything = NaN.")
    (xdoc::li
     "0 * inf = NaN.")
    (xdoc::li
     "If either operand is infinite,
      the result is an infinity with the exclusive-or sign.")
    (xdoc::li
     "Otherwise the result is the rational product;
      a zero product is -0 when the operand signs differ
      and +0 when they agree.")))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (nan1 (float-value-case f1 :nan))
       (nan2 (float-value-case f2 :nan))
       (inf1 (or (float-value-case f1 :posinf)
                 (float-value-case f1 :neginf)))
       (inf2 (or (float-value-case f2 :posinf)
                 (float-value-case f2 :neginf)))
       (n0-1 (float-value-case f1 :neg0))
       (n0-2 (float-value-case f2 :neg0))
       (rat1 (float-value-case f1 :ratio))
       (rat2 (float-value-case f2 :ratio))
       (neg1 (or n0-1
                 (float-value-case f1 :neginf)
                 (and rat1 (< (float-value-ratio->ratio f1) 0))))
       (neg2 (or n0-2
                 (float-value-case f2 :neginf)
                 (and rat2 (< (float-value-ratio->ratio f2) 0))))
       (neg-res (xor neg1 neg2))
       (zero1 (or n0-1
                  (and rat1 (= (float-value-ratio->ratio f1) 0))))
       (zero2 (or n0-2
                  (and rat2 (= (float-value-ratio->ratio f2) 0))))
       (fval
        (cond
          ;; 1. NaN * anything = NaN
          ((or nan1 nan2) (float-value-nan))
          ;; 2. 0 * inf = NaN
          ((or (and zero1 inf2) (and inf1 zero2)) (float-value-nan))
          ;; 3. inf * anything else = inf
          ((or inf1 inf2) (if neg-res
                              (float-value-neginf)
                            (float-value-posinf)))
          ;; 4. standard rational addition with -0 = 0
          ;; NOTE: although -0 is treated like 0 in terms of computation, it's
          ;; still considered to be a negative number, so for example (-0)*5=-0
          ;; and (-0)*(-5)=0. Regardless, neg-res already handles the sign of
          ;; the result so we can just treat it like 0.
          (t (b* ((r1 (if n0-1
                          0
                        (float-value-ratio->ratio f1)))
                  (r2 (if n0-2
                          0
                        (float-value-ratio->ratio f2)))
                  (res (* r1 r2)))
               (if (and (= res 0) neg-res)
                   (float-value-neg0)
                 (float-value-ratio res)))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-mul
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-div ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float division."
  :long
  (xdoc::topstring
   (xdoc::p
    "Finite values are divided as exact rationals
     (see @(see primitives-evaluation) for the float model).
     Unlike integer division, division by zero is not an error:
     it follows [impl].
     The sign of an infinite or zero result is
     the exclusive-or of the operand signs
     (negative zero counts as negative).
     The special cases follow [impl]:")
   (xdoc::ul
    (xdoc::li
     "NaN / anything = NaN; anything / NaN = NaN.")
    (xdoc::li
     "0 / 0 = NaN; inf / inf = NaN.")
    (xdoc::li
     "@('x') / 0 = inf; inf / @('x') = inf,
      where @('x') is a finite rational.")
    (xdoc::li
     "@('x') / inf = 0, where @('x') is a finite rational.")
    (xdoc::li
     "Otherwise the rational quotient;
      a zero quotient is -0 when the operand signs differ
      and +0 when they agree.")))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (nan1 (float-value-case f1 :nan))
       (nan2 (float-value-case f2 :nan))
       (inf1 (or (float-value-case f1 :posinf)
                 (float-value-case f1 :neginf)))
       (inf2 (or (float-value-case f2 :posinf)
                 (float-value-case f2 :neginf)))
       (n0-1 (float-value-case f1 :neg0))
       (n0-2 (float-value-case f2 :neg0))
       (rat1 (float-value-case f1 :ratio))
       (rat2 (float-value-case f2 :ratio))
       (neg1 (or n0-1
                 (float-value-case f1 :neginf)
                 (and rat1 (< (float-value-ratio->ratio f1) 0))))
       (neg2 (or n0-2
                 (float-value-case f2 :neginf)
                 (and rat2 (< (float-value-ratio->ratio f2) 0))))
       (neg-res (xor neg1 neg2))
       (zero1 (or n0-1
                  (and rat1 (= (float-value-ratio->ratio f1) 0))))
       (zero2 (or n0-2
                  (and rat2 (= (float-value-ratio->ratio f2) 0))))
       (fval
        (cond
          ;; 1. NaN / anything = NaN and anything / NaN = NaN
          ((or nan1 nan2) (float-value-nan))
          ;; 2. 0 / 0 = NaN and inf / inf = NaN
          ((or (and zero1 zero2) (and inf1 inf2)) (float-value-nan))
          ;; 3. anything else / 0 = inf and inf / anything else = inf
          ((or zero2 inf1) (if neg-res
                               (float-value-neginf)
                             (float-value-posinf)))
          ;; 4. anything else / inf = 0
          (inf2 (if neg-res (float-value-neg0) (float-value-ratio 0)))
          ;; 5. standard rational addition with -0 = 0
          ;; NOTE: similar to prim-float-mul.
          (t (b* ((r1 (if n0-1
                          0
                        (float-value-ratio->ratio f1)))
                  (r2 (float-value-ratio->ratio f2))
                  (res (/ r1 r2)))
               (if (and (= res 0) neg-res)
                   (float-value-neg0)
                 (float-value-ratio res)))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-div
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-expt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float exponentiation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Exponentiation @('base ** exponent').
     The base may be any float value
     and the exponent may be any float value
     except a non-integer rational:
     ACL2's @(tsee expt) supports only integer exponents
     and returns an exact rational,
     and a non-integer rational exponent
     would generally yield an irrational result
     that the rational model (see @(see primitives-evaluation))
     cannot represent,
     so that single case errors.")
   (xdoc::p
    "Every other case, including the special values,
     follows [impl]'s Haskell @('**'):")
   (xdoc::ul
    (xdoc::li
     "x ** 0 = 1 for any x, including NaN and the infinities
      (a zero exponent being the integer 0 or negative zero).")
    (xdoc::li
     "1 ** y = 1 for any y; (-1) ** inf = 1.")
    (xdoc::li
     "NaN in the base or exponent otherwise yields NaN.")
    (xdoc::li
     "x ** (+inf) is +inf when the base magnitude exceeds 1
      and +0 when it is below 1;
      x ** (-inf) is the reverse.")
    (xdoc::li
     "For a nonzero integer exponent,
      signed zeros and infinities follow the parity rules
      (e.g. (-0) ** 3 = -0, (-inf) ** (-3) = -0),
      and a finite nonzero rational base
      is raised exactly with @(tsee expt).")))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       ((when (and (float-value-case f2 :ratio)
                   (not (integerp (float-value-ratio->ratio f2)))))
        (reserr nil)) ;; ERROR: non-integer rational
       (nan1 (float-value-case f1 :nan))
       (nan2 (float-value-case f2 :nan))
       (pinf1 (float-value-case f1 :posinf))
       (pinf2 (float-value-case f2 :posinf))
       (ninf1 (float-value-case f1 :neginf))
       (ninf2 (float-value-case f2 :neginf))
       (n0-1 (float-value-case f1 :neg0))
       (n0-2 (float-value-case f2 :neg0))
       (rat1 (float-value-case f1 :ratio))
       (rat2 (float-value-case f2 :ratio))
       (r1 (if rat1 (float-value-ratio->ratio f1) 0))
       (r2 (if rat2 (float-value-ratio->ratio f2) 0))
       (exp-zero (or n0-2 (and rat2 (= r2 0))))
       (abs-base-gt-1 (or pinf1 ninf1 (and rat1 (> (abs r1) 1))))
       (fval
        (cond
          ;; 1. x ** 0 = 1, for any x (including NaN and infinities).
          (exp-zero (float-value-ratio 1))
          ;; 2. 1 ** y = 1, for any y.
          ((and rat1 (= r1 1)) (float-value-ratio 1))
          ;; 3. (-1) ** inf = 1.
          ((and rat1 (= r1 -1) (or pinf2 ninf2)) (float-value-ratio 1))
          ;; 4. NaN otherwise propagates.
          ((or nan1 nan2) (float-value-nan))
          ;; 5. x ** +inf = +inf if |x| > 1 otherwise 0.
          (pinf2 (if abs-base-gt-1 (float-value-posinf) (float-value-ratio 0)))
          ;; 6. x ** -inf = 0 if |x| > 1 otherwise +inf.
          (ninf2 (if abs-base-gt-1 (float-value-ratio 0) (float-value-posinf)))
          ;; 7. y is a nonzero integer:
          ;; 7a. +0 ** y = 0 if y > 0 otherwise +inf.
          ((and rat1 (= r1 0))
           (if (> r2 0) (float-value-ratio 0) (float-value-posinf)))
          ;; 7b. -0 ** y =
          ;;  -> -0 if y > 0 and y is odd,
          ;;  -> 0 if y > 0 and y is even,
          ;;  -> -inf if y < 0 and y is odd, and
          ;;  -> +inf if y < 0 and y is even.
          (n0-1
           (cond ((and (> r2 0) (oddp r2)) (float-value-neg0))
                 ((> r2 0) (float-value-ratio 0))
                 ((oddp r2) (float-value-neginf))
                 (t (float-value-posinf))))
          ;; 7c. +inf ** y = +inf if y > 0 otherwise 0.
          (pinf1 (if (> r2 0) (float-value-posinf) (float-value-ratio 0)))
          ;; 7d. -inf ** y =
          ;;  -> -inf if y > 0 and y is odd,
          ;;  -> +inf if y > 0 and y is even,
          ;;  -> -0 if y < 0 and y is odd, and
          ;;  -> +0 if y < 0 and y is even.
          (ninf1
           (cond ((and (> r2 0) (oddp r2)) (float-value-neginf))
                 ((> r2 0) (float-value-posinf))
                 ((oddp r2) (float-value-neg0))
                 (t (float-value-ratio 0))))
          ;; 7e. standard case.
          (t (float-value-ratio (expt r1 r2))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-expt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-max ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float maximum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s Haskell @('max'):
     @('max x y = if x <= y then y else x'),
     where @('<=') is the IEEE comparison
     in which any comparison with NaN is false.
     The result is therefore order-dependent on NaN:
     @('max NaN y') is NaN but @('max x NaN') is x.
     Since negative and positive zero compare equal,
     a tie returns the second operand."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (fval
        (cond
          ;; 1. max x y = x when either x or y is NaN
          ((or (float-value-case f1 :nan) (float-value-case f2 :nan)) f1)
          ;; 2. max +inf y = +inf and max x -inf = x
          ((or (float-value-case f1 :posinf) (float-value-case f2 :neginf)) f1)
          ;; 3. max -inf y = y and max x +inf = +inf
          ((or (float-value-case f1 :neginf) (float-value-case f2 :posinf)) f2)
          ;; 4. standard case
          (t (b* ((r1 (if (float-value-case f1 :neg0)
                          0
                        (float-value-ratio->ratio f1)))
                  (r2 (if (float-value-case f2 :neg0)
                          0
                        (float-value-ratio->ratio f2)))
                  (res (<= r1 r2)))
               (if res f2 f1))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-max
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-min ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float minimum."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s Haskell @('min'):
     @('min x y = if x <= y then x else y'),
     where @('<=') is the IEEE comparison
     in which any comparison with NaN is false.
     The result is therefore order-dependent on NaN:
     @('min NaN y') is y but @('min x NaN') is NaN.
     Since negative and positive zero compare equal,
     a tie returns the first operand."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (fval
        (cond
          ;; 1. min x y = y when either x or y is NaN
          ((or (float-value-case f1 :nan) (float-value-case f2 :nan)) f2)
          ;; 2. min +inf y = y and min x -inf = -inf
          ((or (float-value-case f1 :posinf) (float-value-case f2 :neginf)) f2)
          ;; 3. min -inf y = -inf and min x +inf = x
          ((or (float-value-case f1 :neginf) (float-value-case f2 :posinf)) f1)
          ;; 4. standard case
          (t (b* ((r1 (if (float-value-case f1 :neg0)
                          0
                        (float-value-ratio->ratio f1)))
                  (r2 (if (float-value-case f2 :neg0)
                          0
                        (float-value-ratio->ratio f2)))
                  (res (<= r1 r2)))
               (if res f1 f2))))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-float-min
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-sqrt ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float square root."
  :long
  (xdoc::topstring
   (xdoc::p
    "Square root is currently a stub that always errors.")
   (xdoc::p
    "The difficulty is that our float model
     represents finite values as exact rationals
     (see @(see primitives-evaluation)),
     but the square root of a rational is in general irrational.
     So the exact result is not representable as a @(tsee float-value).")
   (xdoc::p
    "[impl] computes square roots with Haskell's @('sqrt'),
     which maps onto the IEEE-754 hardware/library square root:
     it returns the correctly-rounded single-precision float
     nearest the true result.
     That is possible only because
     Haskell's @('Float') is finite-precision floating point,
     which accepts rounding;
     the irrational answer is approximated
     by the nearest representable float.
     Our exact-rational model has
     no notion of a nearest representable value to round to,
     so we cannot reproduce this without first committing to
     a concrete float format and rounding rule,
     a decision Remora has not yet made.
     We therefore defer the implementation and error for now."))
  (b* (((ok &) (check-expr-value-float val1)))
    (reserr nil))

  ///

  (defret expr-value-wfp-of-prim-float-sqrt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-float-eq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float equality."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s IEEE-754 equality, which is not reflexive:
     NaN is equal to nothing, including itself,
     so @('NaN == NaN') is false.
     Negative zero and positive zero compare equal."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (float-value-case f1
          :nan nil
          :posinf (float-value-case f2 :posinf)
          :neginf (float-value-case f2 :neginf)
          :neg0 (or (float-value-case f2 :neg0)
                    (and (float-value-case f2 :ratio)
                         (= (float-value-ratio->ratio f2) 0)))
          :ratio (or (and (float-value-case f2 :neg0)
                          (= f1.ratio 0))
                     (and (float-value-case f2 :ratio)
                          (= f1.ratio (float-value-ratio->ratio f2)))))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-float-eq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-neq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float inequality."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s IEEE-754 equality, which is not reflexive:
     NaN is equal to nothing, including itself,
     so @('NaN != NaN') is true.
     Negative zero and positive zero compare equal."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (not (float-value-case f1
               :nan nil
               :posinf (float-value-case f2 :posinf)
               :neginf (float-value-case f2 :neginf)
               :neg0 (or (float-value-case f2 :neg0)
                         (and (float-value-case f2 :ratio)
                              (= (float-value-ratio->ratio f2) 0)))
               :ratio (or (and (float-value-case f2 :neg0)
                               (= f1.ratio 0))
                          (and (float-value-case f2 :ratio)
                               (= f1.ratio (float-value-ratio->ratio f2))))))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-float-neq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-lt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float less-than comparison."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s IEEE-754 less-than comparison:
     NaN is unordered,
     so any comparison involving NaN is false.
     Negative zero and positive zero compare equal,
     so @('-0 < +0') is false."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (float-value-case f1
          :nan    nil
          :posinf nil
          :neginf (not (or (float-value-case f2 :neginf)
                           (float-value-case f2 :nan)))
          :neg0 (or (float-value-case f2 :posinf)
                    (and (float-value-case f2 :ratio)
                         (< 0 (float-value-ratio->ratio f2))))
          :ratio (or (float-value-case f2 :posinf)
                     (and (float-value-case f2 :neg0)
                          (< f1.ratio 0))
                     (and (float-value-case f2 :ratio)
                          (< f1.ratio (float-value-ratio->ratio f2)))))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-float-lt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-gt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float greater-than comparison."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s IEEE-754 greater-than comparison:
     NaN is unordered,
     so any comparison involving NaN is false.
     Negative zero and positive zero compare equal,
     so @('+0 > -0') is false."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (float-value-case f1
          :nan    nil
          :posinf (not (or (float-value-case f2 :posinf)
                           (float-value-case f2 :nan)))
          :neginf nil
          :neg0 (or (float-value-case f2 :neginf)
                    (and (float-value-case f2 :ratio)
                         (> 0 (float-value-ratio->ratio f2))))
          :ratio (or (float-value-case f2 :neginf)
                     (and (float-value-case f2 :neg0)
                          (> f1.ratio 0))
                     (and (float-value-case f2 :ratio)
                          (> f1.ratio (float-value-ratio->ratio f2)))))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-float-gt
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-leq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float less-than-or-equal-to comparison."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s IEEE-754 less-than-or-equal comparison:
     NaN is unordered,
     so any comparison involving NaN is false.
     Negative zero and positive zero compare equal,
     so @('-0 <= +0') and @('+0 <= -0') are both true."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (float-value-case f1
          :nan    nil
          :posinf (float-value-case f2 :posinf)
          :neginf (not (float-value-case f2 :nan))
          :neg0 (or (float-value-case f2 :posinf)
                    (float-value-case f2 :neg0)
                    (and (float-value-case f2 :ratio)
                         (<= 0 (float-value-ratio->ratio f2))))
          :ratio (or (float-value-case f2 :posinf)
                     (and (float-value-case f2 :neg0)
                          (<= f1.ratio 0))
                     (and (float-value-case f2 :ratio)
                          (<= f1.ratio (float-value-ratio->ratio f2)))))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-float-leq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-geq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float greater-than-or-equal-to comparison."
  :long
  (xdoc::topstring
   (xdoc::p
    "Follows [impl]'s IEEE-754 greater-than-or-equal comparison:
     NaN is unordered,
     so any comparison involving NaN is false.
     Negative zero and positive zero compare equal,
     so @('-0 >= +0') and @('+0 >= -0') are both true."))
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (float-value-case f1
          :nan    nil
          :posinf (not (float-value-case f2 :nan))
          :neginf (float-value-case f2 :neginf)
          :neg0 (or (float-value-case f2 :neginf)
                    (float-value-case f2 :neg0)
                    (and (float-value-case f2 :ratio)
                         (>= 0 (float-value-ratio->ratio f2))))
          :ratio (or (float-value-case f2 :neginf)
                     (and (float-value-case f2 :neg0)
                          (>= f1.ratio 0))
                     (and (float-value-case f2 :ratio)
                          (>= f1.ratio (float-value-ratio->ratio f2)))))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-float-geq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-float-truncate ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float truncation to integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "Float-to-integer truncation uses ACL2's @(tsee truncate),
     which rounds towards zero.
     This is consistent with [impl],
     which uses Haskell's @('truncate')."))
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int
                                (int-value (truncate fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil)))

  ///

  (defret expr-value-wfp-of-prim-float-truncate
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-round ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float rounding to integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "Float-to-integer rounding uses ACL2's @(tsee round),
     which rounds to the nearest integer,
     with ties going to the even integer.
     This is consistent with [impl],
     which uses Haskell's @('round')."))
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int
                                (int-value (round fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil)))

  ///

  (defret expr-value-wfp-of-prim-float-round
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-ceiling ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float ceiling to integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "Float-to-integer ceiling uses ACL2's @(tsee ceiling),
     which rounds towards positive infinity.
     This is consistent with [impl],
     which uses Haskell's @('ceiling')."))
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int
                                (int-value (ceiling fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil)))

  ///

  (defret expr-value-wfp-of-prim-float-ceiling
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-float-floor ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float floor to integer."
  :long
  (xdoc::topstring
   (xdoc::p
    "Float-to-integer floor uses ACL2's @(tsee floor),
     which rounds towards minus infinity.
     This is consistent with [impl],
     which uses Haskell's @('floor')."))
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int
                                (int-value (floor fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil)))

  ///

  (defret expr-value-wfp-of-prim-float-floor
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-bool-not ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean negation."
  (b* (((ok b1) (check-expr-value-bool val1))
       (bval (not b1)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-bool-not
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-bool-and ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean conjunction."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (and b1 b2)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-bool-and
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-bool-or ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean inclusive disjunction."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (or b1 b2)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-bool-or
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-bool-eq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean equality."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (iff b1 b2)))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-bool-eq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-bool-neq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean inequality."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (not (iff b1 b2))))
    (expr-value-base (base-value-bool bval)))

  ///

  (defret expr-value-wfp-of-prim-bool-neq
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-bool-to-int ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean conversion to integer."
  (b* (((ok b1) (check-expr-value-bool val1))
       (ival (int-value (if b1 1 0))))
    (expr-value-base (base-value-int ival)))

  ///

  (defret expr-value-wfp-of-prim-bool-to-int
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;

(define prim-bool-to-float ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean conversion to float."
  (b* (((ok b1) (check-expr-value-bool val1))
       (fval (float-value-ratio (if b1 1 0))))
    (expr-value-base (base-value-float fval)))

  ///

  (defret expr-value-wfp-of-prim-bool-to-float
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-head ((tval type-valuep)
                   (d natp)
                   (s nat-listp)
                   (val1 expr-valuep))
  :guard (expr-value-wfp val1)
  :returns (val expr-value-resultp)
  :short "Evaluation of array head."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the fully instantiated @('head') operation
     (see the @(':head-t-d-s') summand of @(tsee primop-value)):
     @('tval'), @('d'), and @('s') are the instantiation values,
     and @('val1') is the argument cell.
     According to the instantiated type of the operation,
     the argument cell is an array
     whose dimensions are the dimension @('d+1') followed by the shape @('s'),
     and the result is the first element, which is of shape @('s').
     The guard requires the argument cell to be well-formed;
     we defensively check that it has the expected dimensions.")
   (xdoc::p
    "The type value @('tval') is currently unused,
     because our well-formedness checks on expression values
     currently concern dimensions but not types;
     it will be used to further check the argument cell
     when those checks are extended to types."))
  (declare (ignore tval))
  (b* ((d (lnfix d))
       (s (nat-list-fix s))
       ((unless (equal (dims-of-expr-value val1) (cons (1+ d) s)))
        (reserr nil))
       ((unless (expr-value-case val1 :vector))
        (reserr nil))
       (elems (expr-value-vector->elems val1))
       ((unless (consp elems)) (reserr nil)))
    (car elems))

  ///

  (defret expr-value-wfp-of-prim-head
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hyp (expr-value-wfp val1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-tail ((tval type-valuep)
                   (d natp)
                   (s nat-listp)
                   (val1 expr-valuep))
  :guard (expr-value-wfp val1)
  :returns (val expr-value-resultp)
  :short "Evaluation of array tail."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the fully instantiated @('tail') operation
     (see the @(':tail-t-d-s') summand of @(tsee primop-value)):
     @('tval'), @('d'), and @('s') are the instantiation values,
     and @('val1') is the argument cell.
     According to the instantiated type of the operation,
     the argument cell is an array
     whose dimensions are the dimension @('d+1') followed by the shape @('s'),
     and the result is the array after removing the first element,
     whose dimensions are
     the dimension @('d') followed by the shape @('s').
     The guard requires the argument cell to be well-formed;
     we defensively check that it has the expected dimensions.")
   (xdoc::p
    "The type value @('tval') is currently only used
     for when the output is an empty array
     and not for checking well-formedness,
     because our well-formedness checks on expression values
     currently concern dimensions but not types;
     it will be used to further check the argument cell
     when those checks are extended to types."))
  (b* ((d (lnfix d))
       (s (nat-list-fix s))
       ((unless (equal (dims-of-expr-value val1) (cons (1+ d) s)))
        (reserr nil))
       ((unless (expr-value-case val1 :vector))
        (reserr nil))
       (elems (expr-value-vector->elems val1))
       ((unless (consp elems)) (reserr nil))
       (tail (cdr elems)))
    (if (consp tail)
        (expr-value-vector tail)
      (expr-value-vector-empty s tval)))

  ///

  (defret expr-value-wfp-of-prim-tail
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hyp (expr-value-wfp val1)
    :hints (("Goal" :in-theory (e/d (dims-of-expr-value-list-of-cdr)
                                    (cdr-of-dims-of-expr-value-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-length ((tval type-valuep)
                     (d natp)
                     (s nat-listp)
                     (val1 expr-valuep))
  :guard (expr-value-wfp val1)
  :returns (val expr-value-resultp)
  :short "Evaluation of array length."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the fully instantiated @('length') operation
     (see the @(':length-t-d-s') summand of @(tsee primop-value)):
     @('tval'), @('d'), and @('s') are the instantiation values,
     and @('val1') is the argument cell.
     According to the instantiated type of the operation,
     the argument cell is an array
     whose dimensions are the dimension @('d') followed by the shape @('s'),
     and the result is @('d'), as a scalar integer value.
     The guard requires the argument cell to be well-formed;
     we defensively check that it has the expected dimensions.")
   (xdoc::p
    "The type value @('tval') is currently unused,
     because our well-formedness checks on expression values
     currently concern dimensions but not types;
     it will be used to further check the argument cell
     when those checks are extended to types."))
  (declare (ignore tval))
  (b* ((d (lnfix d))
       (s (nat-list-fix s))
       ((unless (equal (dims-of-expr-value val1) (cons d s)))
        (reserr nil)))
    (expr-value-base (base-value-int (int-value d))))

  ///

  (defret expr-value-wfp-of-prim-length
    (implies (not (reserrp val))
             (expr-value-wfp val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-append ((tval type-valuep)
                     (m natp)
                     (n natp)
                     (s nat-listp)
                     (val1 expr-valuep)
                     (val2 expr-valuep))
  :guard (and (expr-value-wfp val1) (expr-value-wfp val2))
  :returns (val expr-value-resultp)
  :short "Evaluation of array append."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the fully instantiated @('append') operation
     (see the @(':append-t-m-n-s') summand of @(tsee primop-value)):
     @('tval'), @('m'), @('n'), and @('s') are the instantiation values,
     and @('val1') and @('val2') are the argument cells.
     According to the instantiated type of the operation,
     the argument cells are arrays
     whose dimensions are the dimensions @('m') and @('n') respectively,
     each followed by the shape @('s'),
     and the result is the concatenation of the two arrays,
     whose dimensions are the dimension @('m+n') followed by the shape @('s').
     The guard requires the argument cells to be well-formed;
     we defensively check that they have the expected dimensions.")
   (xdoc::p
    "Since @('m') and @('n') may be 0,
     the argument cells may be empty arrays,
     which are not @(':vector') values and contribute no elements.
     The type value @('tval') is currently only used
     for when the output is an empty array
     and not for checking well-formedness,
     because our well-formedness checks on expression values
     currently concern dimensions but not types;
     it will be used to further check the argument cells
     when those checks are extended to types."))
  (b* ((m (lnfix m)) (n (lnfix n)) (s (nat-list-fix s))
       ((unless (equal (dims-of-expr-value val1) (cons m s))) (reserr nil))
       ((unless (equal (dims-of-expr-value val2) (cons n s))) (reserr nil))
       (elems1 (expr-value-vector-elements val1))
       (elems2 (expr-value-vector-elements val2))
       (elems (append elems1 elems2)))
    (if (consp elems)
        (expr-value-vector elems)
      (expr-value-vector-empty s tval)))
  :guard-hints
  (("Goal" :in-theory (enable expr-value-vectorp-to-consp-of-dims)))

  ///

  (defret expr-value-wfp-of-prim-append
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hyp (and (expr-value-wfp val1)
              (expr-value-wfp val2))
    :hints (("Goal"
             :in-theory
             (e/d (dims-of-expr-value-vector-elements-to-repeat
                   expr-value-vectorp-to-consp-of-dims
                   car-of-repeat
                   car/cdr-when-equal-cons)
                  (car-of-dims-of-expr-value-list))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-reverse ((tval type-valuep)
                      (d natp)
                      (s nat-listp)
                      (val1 expr-valuep))
  :guard (expr-value-wfp val1)
  :returns (val expr-value-resultp)
  :short "Evaluation of array reverse."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the semantics of the fully instantiated @('reverse') operation
     (see the @(':reverse-t-d-s') summand of @(tsee primop-value)):
     @('tval'), @('d'), and @('s') are the instantiation values,
     and @('val1') is the argument cell.
     According to the instantiated type of the operation,
     the argument cell is an array
     whose dimensions are the dimension @('d') followed by the shape @('s'),
     and the result is the array with its elements in reverse order,
     with the same dimensions.
     The guard requires the argument cell to be well-formed;
     we defensively check that it has the expected dimensions.")
   (xdoc::p
    "We reverse the order of the elements of the cell,
     i.e. we reverse the array along its leading axis.
     [impl] instead reverses the flattened list
     of all the atoms of the array,
     which differs from our semantics
     when the shape @('s') is not empty.")
   (xdoc::p
    "Since @('d') may be 0, the argument cell may be an empty array,
     which is not a @(':vector') value and has no elements.
     The type value @('tval') is currently only used
     for when the output is an empty array
     and not for checking well-formedness,
     because our well-formedness checks on expression values
     currently concern dimensions but not types;
     it will be used to further check the argument cell
     when those checks are extended to types."))
  (b* ((d (lnfix d)) (s (nat-list-fix s))
       ((unless (equal (dims-of-expr-value val1) (cons d s))) (reserr nil))
       (elems (if (expr-value-case val1 :vector)
                  (expr-value-vector->elems val1)
                nil))
       (relems (rev elems)))
    (if (consp relems)
        (expr-value-vector relems)
      (expr-value-vector-empty s tval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-primop-fun ((op primop-valuep) (args expr-value-listp))
  :guard (and (primop-value-funp op)
              (expr-value-list-wfp args))
  :returns (val expr-value-resultp)
  :short "Evaluate the application of a primitive operation
          to its argument cells."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart, for primitive operations,
     of evaluating the body of a lambda abstraction:
     it is called by @(tsee eval-app-cell)
     on a scalar primitive operation and its scalar argument cells,
     after the rank-polymorphic lifting.")
   (xdoc::p
    "The guard requires the value to be applicable to expression values
     (see @(tsee primop-value-funp))
     and the argument cells to be well-formed.
     We check that the value is applied to the right number of argument cells;
     then we dispatch on the operation,
     calling the @('prim-...') function that defines the operation's semantics.
     Anything else is an error.")
   (xdoc::p
    "The result is well-formed when it is not an error,
     because each @('prim-...') function returns
     a scalar base value on success."))
  (b* ((args (expr-value-list-fix args))
       ((unless (equal (len args) (arity-of-primop-value-fun op)))
        (reserr nil)))
    (primop-value-case
     op
     :int-add (prim-int-add (first args) (second args))
     :int-sub (prim-int-sub (first args) (second args))
     :int-mul (prim-int-mul (first args) (second args))
     :int-div (prim-int-div (first args) (second args))
     :int-expt (prim-int-expt (first args) (second args))
     :int-mod (prim-int-mod (first args) (second args))
     :int-max (prim-int-max (first args) (second args))
     :int-min (prim-int-min (first args) (second args))
     :int-bit-and (prim-int-bit-and (first args) (second args))
     :int-bit-or (prim-int-bit-or (first args) (second args))
     :int-bit-xor (prim-int-bit-xor (first args) (second args))
     :int-shl (prim-int-shl (first args) (second args))
     :int-shr (prim-int-shr (first args) (second args))
     :int-bit-not (prim-int-bit-not (first args))
     :int-popc (prim-int-popc (first args))
     :int-eq (prim-int-eq (first args) (second args))
     :int-neq (prim-int-neq (first args) (second args))
     :int-lt (prim-int-lt (first args) (second args))
     :int-gt (prim-int-gt (first args) (second args))
     :int-leq (prim-int-leq (first args) (second args))
     :int-geq (prim-int-geq (first args) (second args))
     :int-to-float (prim-int-to-float (first args))
     :int-to-bool (prim-int-to-bool (first args))
     :float-add (prim-float-add (first args) (second args))
     :float-sub (prim-float-sub (first args) (second args))
     :float-mul (prim-float-mul (first args) (second args))
     :float-div (prim-float-div (first args) (second args))
     :float-expt (prim-float-expt (first args) (second args))
     :float-max (prim-float-max (first args) (second args))
     :float-min (prim-float-min (first args) (second args))
     :float-sqrt (prim-float-sqrt (first args))
     :float-eq (prim-float-eq (first args) (second args))
     :float-neq (prim-float-neq (first args) (second args))
     :float-lt (prim-float-lt (first args) (second args))
     :float-gt (prim-float-gt (first args) (second args))
     :float-leq (prim-float-leq (first args) (second args))
     :float-geq (prim-float-geq (first args) (second args))
     :float-truncate (prim-float-truncate (first args))
     :float-round (prim-float-round (first args))
     :float-ceiling (prim-float-ceiling (first args))
     :float-floor (prim-float-floor (first args))
     :bool-not (prim-bool-not (first args))
     :bool-and (prim-bool-and (first args) (second args))
     :bool-or (prim-bool-or (first args) (second args))
     :bool-eq (prim-bool-eq (first args) (second args))
     :bool-neq (prim-bool-neq (first args) (second args))
     :bool-to-int (prim-bool-to-int (first args))
     :bool-to-float (prim-bool-to-float (first args))
     :head (prog2$ (impossible) (reserr nil))
     :head-t (prog2$ (impossible) (reserr nil))
     :head-t-d-s (prim-head op.tval op.dval op.sval (first args))
     :tail (prog2$ (impossible) (reserr nil))
     :tail-t (prog2$ (impossible) (reserr nil))
     :tail-t-d-s (prim-tail op.tval op.dval op.sval (first args))
     :length (prog2$ (impossible) (reserr nil))
     :length-t (prog2$ (impossible) (reserr nil))
     :length-t-d-s (prim-length op.tval op.dval op.sval (first args))
     :append (prog2$ (impossible) (reserr nil))
     :append-t (prog2$ (impossible) (reserr nil))
     :append-t-m-n-s (prim-append op.tval op.mval op.nval op.sval
                                  (first args) (second args))
     :reverse (prog2$ (impossible) (reserr nil))
     :reverse-t (prog2$ (impossible) (reserr nil))
     :reverse-t-d-s (prim-reverse op.tval op.dval op.sval (first args))))
  :guard-hints (("Goal" :in-theory (enable primop-value-funp
                                           arity-of-primop-value-fun
                                           type-of-primop-value-fun)))

  ///

  (defret expr-value-wfp-of-eval-primop-fun
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hyp (expr-value-list-wfp args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-primop-tfun ((op primop-valuep) (tvals type-value-listp))
  :guard (primop-value-tfunp op)
  :returns (val expr-value-resultp)
  :short "Evaluate the application of a primitive operation value
          to type values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart, for primitive operations,
     of applying a type lambda abstraction to type values:
     it is called by @(tsee eval-tapp)
     on a scalar primitive operation value
     and the type argument values.")
   (xdoc::p
    "The guard requires the value to be applicable to type values
     (see @(tsee primop-value-tfunp)).
     We check that the type values match, in number and kinds,
     the type parameters of the operation,
     i.e. the ones in the operation's type in @(tsee primop-types);
     then we construct the next instantiation stage of the operation,
     which stores the type values received.
     Anything else is an error."))
  (primop-value-case
   op
   :head (b* (((unless (type-values-match-type-vars-p
                        tvals
                        (list (type-var-atom "t"))))
               (reserr nil)))
           (expr-value-primop (primop-value-head-t (first tvals))))
   :tail (b* (((unless (type-values-match-type-vars-p
                        tvals
                        (list (type-var-atom "t"))))
               (reserr nil)))
           (expr-value-primop (primop-value-tail-t (first tvals))))
   :length (b* (((unless (type-values-match-type-vars-p
                          tvals
                          (list (type-var-atom "t"))))
                 (reserr nil)))
             (expr-value-primop (primop-value-length-t (first tvals))))
   :append (b* (((unless (type-values-match-type-vars-p
                          tvals
                          (list (type-var-atom "t"))))
                 (reserr nil)))
             (expr-value-primop (primop-value-append-t (first tvals))))
   :reverse (b* (((unless (type-values-match-type-vars-p
                           tvals
                           (list (type-var-atom "t"))))
                  (reserr nil)))
              (expr-value-primop (primop-value-reverse-t (first tvals))))
   :otherwise (prog2$ (impossible) (reserr nil)))
  :guard-hints (("Goal" :in-theory (enable primop-value-tfunp
                                           type-values-match-type-vars-p)))

  ///

  (defret expr-value-wfp-of-eval-primop-tfun
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hints (("Goal" :in-theory (enable expr-value-wfp
                                       check-dims-of-expr-value)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-primop-ifun ((op primop-valuep) (ivals ispace-value-listp))
  :guard (primop-value-ifunp op)
  :returns (val expr-value-resultp)
  :short "Evaluate the application of a primitive operation value
          to ispace values."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart, for primitive operations,
     of applying an ispace lambda abstraction to ispace values:
     it is called by @(tsee eval-iapp)
     on a scalar primitive operation value
     and the ispace argument values.")
   (xdoc::p
    "The guard requires the value to be applicable to ispace values
     (see @(tsee primop-value-ifunp)).
     We check that the ispace values match, in number and sorts,
     the ispace parameters of the operation,
     i.e. the ones in the operation's type in @(tsee primop-types);
     then we construct the next instantiation stage of the operation,
     which stores the ispace values received
     (a dimension and a shape
     for @('head'), @('tail'), @('length'), and @('reverse');
     two dimensions and a shape for @('append')),
     along with the previously received type values.
     Anything else is an error."))
  (primop-value-case
   op
   :head-t (b* (((unless (ispace-values-match-ispace-vars-p
                          ivals
                          (list (ispace-var-dim "d")
                                (ispace-var-shape "s"))))
                 (reserr nil)))
             (expr-value-primop
              (make-primop-value-head-t-d-s
               :tval op.tval
               :dval (ispace-value-dim->val (first ivals))
               :sval (ispace-value-shape->val (second ivals)))))
   :tail-t (b* (((unless (ispace-values-match-ispace-vars-p
                          ivals
                          (list (ispace-var-dim "d")
                                (ispace-var-shape "s"))))
                 (reserr nil)))
             (expr-value-primop
              (make-primop-value-tail-t-d-s
               :tval op.tval
               :dval (ispace-value-dim->val (first ivals))
               :sval (ispace-value-shape->val (second ivals)))))
   :length-t (b* (((unless (ispace-values-match-ispace-vars-p
                            ivals
                            (list (ispace-var-dim "d")
                                  (ispace-var-shape "s"))))
                   (reserr nil)))
               (expr-value-primop
                (make-primop-value-length-t-d-s
                 :tval op.tval
                 :dval (ispace-value-dim->val (first ivals))
                 :sval (ispace-value-shape->val (second ivals)))))
   :append-t (b* (((unless (ispace-values-match-ispace-vars-p
                            ivals
                            (list (ispace-var-dim "m")
                                  (ispace-var-dim "n")
                                  (ispace-var-shape "s"))))
                   (reserr nil)))
               (expr-value-primop
                (make-primop-value-append-t-m-n-s
                 :tval op.tval
                 :mval (ispace-value-dim->val (first ivals))
                 :nval (ispace-value-dim->val (second ivals))
                 :sval (ispace-value-shape->val (third ivals)))))
   :reverse-t (b* (((unless (ispace-values-match-ispace-vars-p
                             ivals
                             (list (ispace-var-dim "d")
                                   (ispace-var-shape "s"))))
                    (reserr nil)))
                (expr-value-primop
                 (make-primop-value-reverse-t-d-s
                  :tval op.tval
                  :dval (ispace-value-dim->val (first ivals))
                  :sval (ispace-value-shape->val (second ivals)))))
   :otherwise (prog2$ (impossible) (reserr nil)))
  :guard-hints (("Goal" :in-theory (enable primop-value-ifunp
                                           ispace-values-match-ispace-vars-p)))

  ///

  (defret expr-value-wfp-of-eval-primop-ifun
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hints (("Goal" :in-theory (enable expr-value-wfp
                                       check-dims-of-expr-value)))))
