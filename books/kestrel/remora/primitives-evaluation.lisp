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
(include-book "kestrel/fty/boolean-result" :dir :system)

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
               @(tsee prim-int-mod), @(tsee prim-int-max),
               @(tsee prim-int-min).")
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
    "The float primitives currently implemented are
     @(tsee prim-float-add), @(tsee prim-float-sub), @(tsee prim-float-mul),
     @(tsee prim-float-div), @(tsee prim-float-truncate),
     @(tsee prim-float-round), @(tsee prim-float-ceiling),
     and @(tsee prim-float-floor).")
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
  :long "<p>Left shift uses ACL2's @(tsee ash) with a non-negative shift
  amount, erroring on a negative shift amount. Because integers are modeled as
  unbounded (see @(see primitives-evaluation)), the shift never overflows: no
  high-order bits are lost. This differs from [impl], which uses Haskell's
  fixed-width @('shiftL'), where bits shifted past the word width are
  discarded.</p>"
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

(define prim-int-popc ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of integer pop count."
  :long "<p>Pop count (the number of set bits) uses ACL2's @(tsee logcount).
  Only non-negative inputs are accepted; a negative input is an error. On a
  negative integer, [impl]'s Haskell @('popCount') counts the set bits of the
  fixed-width two's-complement representation (a finite, width-dependent count),
  whereas @(tsee logcount) counts the bits of the unbounded magnitude. Because
  integers are modeled as unbounded (see @(see primitives-evaluation)), there is
  no fixed width to match, so the behavior on negative inputs would differ from
  [impl]; we therefore restrict to non-negative inputs for now.</p>"
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-float-add ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float addition."
  :long "<p>Finite values are added as exact rationals
  (see @(see primitives-evaluation) for the float model).
  The special cases follow [impl]:</p>
  <ul>
   <li>NaN + anything = NaN.</li>
   <li>(+inf) + (-inf) = NaN.</li>
   <li>(+inf) + @('x') = +inf, where @('x') is a finite rational.</li>
   <li>(-inf) + @('x') = -inf, where @('x') is a finite rational.</li>
   <li>(-0) + (-0) = -0; every other sum that is zero is +0.</li>
  </ul>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-sub ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float subtraction."
  :long "<p>Finite values are subtracted as exact rationals
  (see @(see primitives-evaluation) for the float model).
  The special cases follow [impl]:</p>
  <ul>
   <li>NaN - anything = NaN; anything - NaN = NaN.</li>
   <li>(+inf) - (+inf) = NaN; (-inf) - (-inf) = NaN.</li>
   <li>(+inf) - @('x') = +inf; @('x') - (-inf) = +inf, where @('x') is a finite
  rational.</li>
   <li>(-inf) - @('x') = -inf; @('x') - (+inf) = -inf, where @('x') is a finite
  rational.</li>
   <li>(-0) - (+0) = -0; every other difference that is zero is +0.</li>
  </ul>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-mul ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float multiplication."
  :long "<p>Finite values are multiplied as exact rationals
  (see @(see primitives-evaluation) for the float model).
  The sign of an infinite or zero result is the exclusive-or of the operand
  signs (negative zero counts as negative).
  The special cases follow [impl]:</p>
  <ul>
   <li>NaN * anything = NaN.</li>
   <li>0 * inf = NaN.</li>
   <li>If either operand is infinite, the result is an infinity
       with the exclusive-or sign.</li>
   <li>Otherwise the result is the rational product; a zero product is -0 when
       the operand signs differ and +0 when they agree.</li>
  </ul>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-div ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float division."
  :long "<p>Finite values are divided as exact rationals
  (see @(see primitives-evaluation) for the float model).
  Unlike integer division, division by zero is not an error: it follows
  [impl]. The sign of an infinite or zero result is the exclusive-or of the
  operand signs (negative zero counts as negative).
  The special cases follow [impl]:</p>
  <ul>
   <li>NaN / anything = NaN; anything / NaN = NaN.</li>
   <li>0 / 0 = NaN; inf / inf = NaN.</li>
   <li>@('x') / 0 = inf; inf / @('x') = inf, where @('x') is a finite
  rational.</li>
   <li>@('x') / inf = 0, where @('x') is a finite rational.</li>
   <li>Otherwise the rational quotient; a zero quotient is -0 when the operand
       signs differ and +0 when they agree.</li>
  </ul>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-expt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float exponentiation."
  :long "<p>Exponentiation @('base ** exponent'). The base may be any float
  value and the exponent may be any float value except a non-integer rational:
  ACL2's @(tsee expt) supports only integer exponents and returns an exact
  rational, and a non-integer rational exponent would generally yield an
  irrational result that the rational model (see @(see primitives-evaluation))
  cannot represent, so that single case errors.</p>
  <p>Every other case, including the special values, follows [impl]'s Haskell
  @('**')):</p>
  <ul>
   <li>x ** 0 = 1 for any x, including NaN and the infinities (a zero exponent
       being the integer 0 or negative zero).</li>
   <li>1 ** y = 1 for any y; (-1) ** inf = 1.</li>
   <li>NaN in the base or exponent otherwise yields NaN.</li>
   <li>x ** (+inf) is +inf when the base magnitude exceeds 1 and +0 when it is
       below 1; x ** (-inf) is the reverse.</li>
   <li>For a nonzero integer exponent, signed zeros and infinities follow the
       parity rules (e.g. (-0) ** 3 = -0, (-inf) ** (-3) = -0), and a finite
       nonzero rational base is raised exactly with @(tsee expt).</li>
  </ul>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-max ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float maximum."
  :long "<p>Follows [impl]'s Haskell @('max'):
  @('max x y = if x <= y then y else x'), where @('<=') is the IEEE comparison
  in which any comparison with NaN is false. The result is therefore
  order-dependent on NaN: @('max NaN y') is NaN but @('max x NaN') is x. Since
  negative and positive zero compare equal, a tie returns the second
  operand.</p>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-min ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float minimum."
  :long "<p>Follows [impl]'s Haskell @('min'):
  @('min x y = if x <= y then x else y'), where @('<=') is the IEEE comparison
  in which any comparison with NaN is false. The result is therefore
  order-dependent on NaN: @('min NaN y') is y but @('min x NaN') is NaN. Since
  negative and positive zero compare equal, a tie returns the first
  operand.</p>"
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
    (expr-value-base (base-value-float fval))))

(define prim-float-sqrt ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float square root."
  :long "<p>Square root is currently a stub that always errors.</p>
  <p>The difficulty is that our float model represents finite values as exact
  rationals (see @(see primitives-evaluation)), but the square root of a
  rational is in general irrational. So the exact result is not representable as a
  @(tsee float-value).</p>
  <p>[impl] computes square roots with Haskell's @('sqrt'), which maps onto the
  IEEE-754 hardware/library square root: it returns the correctly-rounded
  single-precision float nearest the true result. That is possible only because
  Haskell's @('Float') is finite-precision floating point, which accepts
  rounding; the irrational answer is approximated by the nearest representable
  float. Our exact-rational model has no notion of a nearest representable value
  to round to, so we cannot reproduce this without first committing to a
  concrete float format and rounding rule, a decision Remora has not yet made.
  We therefore defer the implementation and error for now.</p>"
  (b* (((ok &) (check-expr-value-float val1)))
    (reserr nil)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-float-eq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float equality."
  :long "<p>Follows [impl]'s IEEE-754 equality, which is not reflexive: NaN is
  equal to nothing, including itself, so @('NaN == NaN') is false. Negative zero
  and positive zero compare equal.</p>"
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
    (expr-value-base (base-value-bool bval))))

(define prim-float-neq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float equality."
  :long "<p>Follows [impl]'s IEEE-754 equality, which is not reflexive: NaN is
  equal to nothing, including itself, so @('NaN != NaN') is true. Negative zero
  and positive zero compare equal.</p>"
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
    (expr-value-base (base-value-bool bval))))

(define prim-float-lt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float less-than comparison."
  :long "<p>Follows [impl]'s IEEE-754 less-than comparison: NaN is unordered, so
  any comparison involving NaN is false. Negative zero and positive zero compare
  equal, so @('-0 < +0') is false.</p>"
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
    (expr-value-base (base-value-bool bval))))

(define prim-float-gt ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float greater-than comparison."
  :long "<p>Follows [impl]'s IEEE-754 greater-than comparison: NaN is unordered,
  so any comparison involving NaN is false. Negative zero and positive zero
  compare equal, so @('+0 > -0') is false.</p>"
  (b* (((ok f1) (check-expr-value-float val1))
       ((ok f2) (check-expr-value-float val2))
       (bval
        (float-value-case f1
          :nan    nil
          :posinf (not (or (float-value-case f2 :posinf) (float-value-case f2 :nan)))
          :neginf nil
          :neg0 (or (float-value-case f2 :neginf)
                    (and (float-value-case f2 :ratio) 
                         (> 0 (float-value-ratio->ratio f2))))
          :ratio (or (float-value-case f2 :neginf)
                     (and (float-value-case f2 :neg0) 
                          (> f1.ratio 0))
                     (and (float-value-case f2 :ratio) 
                          (> f1.ratio (float-value-ratio->ratio f2)))))))
    (expr-value-base (base-value-bool bval))))

(define prim-float-leq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float less-than-or-equal-to comparison."
  :long "<p>Follows [impl]'s IEEE-754 less-than-or-equal comparison: NaN is
  unordered, so any comparison involving NaN is false. Negative zero and
  positive zero compare equal, so @('-0 <= +0') and @('+0 <= -0') are both
  true.</p>"
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
    (expr-value-base (base-value-bool bval))))

(define prim-float-geq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float greater-than-or-equal-to comparison."
  :long "<p>Follows [impl]'s IEEE-754 greater-than-or-equal comparison: NaN is
  unordered, so any comparison involving NaN is false. Negative zero and
  positive zero compare equal, so @('-0 >= +0') and @('+0 >= -0') are both
  true.</p>"
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
    (expr-value-base (base-value-bool bval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-float-truncate ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float truncation to integer."
  :long "<p>Float-to-integer truncation uses ACL2's @(tsee truncate), which
  rounds towards zero. This is consistent with [impl], which uses Haskell's
  @('truncate')</p>"
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int (int-value (truncate fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil))))

(define prim-float-round ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float rounding to integer."
  :long "<p>Float-to-integer rounding uses ACL2's @(tsee round), which rounds
  to the nearest integer, with ties going to the even integer. This is
  consistent with [impl], which uses Haskell's @('round')</p>"
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int (int-value (round fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil))))

(define prim-float-ceiling ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float ceiling to integer."
  :long "<p>Float-to-integer ceiling uses ACL2's @(tsee ceiling), which rounds
  towards positive infinity. This is consistent with [impl], which uses
  Haskell's @('ceiling')</p>"
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int (int-value (ceiling fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil))))

(define prim-float-floor ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of float floor to integer."
  :long "<p>Float-to-integer floor uses ACL2's @(tsee floor), which rounds
  towards minus infinity. This is consistent with [impl], which uses Haskell's
  @('floor')</p>"
  (b* (((ok fval) (check-expr-value-float val1)))
    (float-value-case fval
      :ratio  (expr-value-base (base-value-int (int-value (floor fval.ratio 1))))
      :neg0   (expr-value-base (base-value-int (int-value 0)))
      :posinf (reserr nil)
      :neginf (reserr nil)
      :nan    (reserr nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-bool-not ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean negation."
  (b* (((ok b1) (check-expr-value-bool val1))
       (bval (not b1)))
    (expr-value-base (base-value-bool bval))))

(define prim-bool-and ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean conjunction."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (and b1 b2)))
    (expr-value-base (base-value-bool bval))))

(define prim-bool-or ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean inclusive disjunction."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (or b1 b2)))
    (expr-value-base (base-value-bool bval))))

(define prim-bool-eq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean equality."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (iff b1 b2)))
    (expr-value-base (base-value-bool bval))))

(define prim-bool-neq ((val1 expr-valuep) (val2 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean inequality."
  (b* (((ok b1) (check-expr-value-bool val1))
       ((ok b2) (check-expr-value-bool val2))
       (bval (not (iff b1 b2))))
    (expr-value-base (base-value-bool bval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prim-bool-to-int ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean conversion to integer."
  (b* (((ok b1) (check-expr-value-bool val1))
       (ival (int-value (if b1 1 0))))
    (expr-value-base (base-value-int ival))))

(define prim-bool-to-float ((val1 expr-valuep))
  :returns (val expr-value-resultp)
  :short "Evaluation of boolean conversion to float."
  (b* (((ok b1) (check-expr-value-bool val1))
       (fval (float-value-ratio (if b1 1 0))))
    (expr-value-base (base-value-float fval))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define eval-primop ((op primop-valuep) (args expr-value-listp))
  :returns (val expr-value-resultp)
  :short "Evaluate the application of a primitive operation
          to its argument cells."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the dynamic counterpart, for primitive operations,
     of evaluating the body of a lambda abstraction:
     it will be called by @(tsee eval-app-cell)
     on a scalar primitive operation and its scalar argument cells,
     after the rank-polymorphic lifting.")
   (xdoc::p
    "We dispatch on the operation,
     check that it is applied to the right number of argument cells,
     and call the @('prim-...') function
     that defines the operation's semantics.
     Anything else is an error.")
   (xdoc::p
    "The result is well-formed when it is not an error,
     because each @('prim-...') function returns
     a scalar base value on success."))
  (b* ((args (expr-value-list-fix args))
       ((unless (equal (len args) (primop-arity op))) (reserr nil)))
    (primop-value-case
     op
     :int-add (prim-int-add (first args) (second args))
     :int-sub (prim-int-sub (first args) (second args))
     :int-mul (prim-int-mul (first args) (second args))
     :int-div (prim-int-div (first args) (second args))
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
     :bool-not (prim-bool-not (first args))
     :bool-and (prim-bool-and (first args) (second args))
     :bool-or (prim-bool-or (first args) (second args))
     :bool-eq (prim-bool-eq (first args) (second args))
     :bool-neq (prim-bool-neq (first args) (second args))
     :bool-to-int (prim-bool-to-int (first args))
     :bool-to-float (prim-bool-to-float (first args))))
  :guard-hints (("Goal" :in-theory (enable primop-arity primop-type)))

  ///

  (defret expr-value-wfp-of-eval-primop
    (implies (not (reserrp val))
             (expr-value-wfp val))
    :hints (("Goal" :in-theory (enable eval-primop
                                       prim-int-add
                                       prim-int-sub
                                       prim-int-mul
                                       prim-int-div
                                       prim-int-mod
                                       prim-int-max
                                       prim-int-min
                                       prim-int-bit-and
                                       prim-int-bit-or
                                       prim-int-bit-xor
                                       prim-int-shl
                                       prim-int-shr
                                       prim-int-bit-not
                                       prim-int-popc
                                       prim-int-eq
                                       prim-int-neq
                                       prim-int-lt
                                       prim-int-gt
                                       prim-int-leq
                                       prim-int-geq
                                       prim-int-to-float
                                       prim-int-to-bool
                                       prim-bool-not
                                       prim-bool-and
                                       prim-bool-or
                                       prim-bool-eq
                                       prim-bool-neq
                                       prim-bool-to-int
                                       prim-bool-to-float)))))
