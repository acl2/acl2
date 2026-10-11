; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 54: invert-var does not return a multiplicative inverse, and
; inverse-polys treats it as one.
;
; add-inverse-polys (non-linear.lisp:762) computes
; inverted-var = (invert-var var) and hands the pair to inverse-polys
; (non-linear.lisp:426), whose only job is to reciprocate NUMERIC bounds on one
; member and attribute them to the other.  That is sound only if inverted-var is
; exactly 1/var.  invert-var's own comment hedges ("we TRY to return the
; multiplicative inverse"), but every consumer treats it as exact.
;
; For (UNARY-/ x) invert-var returns (varify! x) (non-linear.lisp:166), and
; VARIFY is a POT-LABEL SANITIZER, not an algebraic identity: it strips a leading
; rational factor from a BINARY-* (because (good-pot-varp '(binary-* '3 b)) is
; NIL) and, for a BINARY-+, picks ONE ADDEND -- its own comment says "We have to
; pick one."  Measured:
;   (invert-var '(unary-/ (binary-* '3 b)))                -> B
;   (invert-var '(unary-/ (binary-* '3 (binary-+ a b))))   -> A
;   (invert-var '(unary-/ b))                              -> B          (correct)
;   (invert-var '(unary-/ (binary-* a b)))                 -> (BINARY-* A B)  (correct)
; So inverse-polys reciprocates between 1/(c*b) and b as if b = 1/(1/(c*b)),
; off by the factor c.  Reciprocating an UPPER bound yields a lower bound on b
; that is c-times too large; reciprocating a LOWER bound yields an upper bound
; 1/c-times too small.  Both directions were witnessed.
;
; Gated on non-linear arithmetic only -- add-inverse-polys is called solely from
; add-polys-and-lemmas2-nl (rewrite.lisp:22014).  (set-non-linearp t) is an
; ordinary event.
;
; Fuzzing fixed the exposure: 350 false conjectures over a grammar INCLUDING
; (/ (* c ...)) -> 13 proved, all 13 containing that shape; 1050 false
; conjectures over a grammar EXCLUDING it -> 0 proved.
;
; POLARITY: the MUST-FAILs state the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(set-non-linearp t)

; THE DEFECT, smallest form: two hypotheses, no hints.  FALSE at b = 1/3.
; Path: var-lbd = var-ubd = 1 > 0, so branch A of inverse-polys runs
; bounds-polys1 (non-linear.lisp:525-538), which emits (/ var-ubd) <= inv-var,
; i.e. 1 <= b.
(must-fail
 (defthm bogus-minimal
   (implies (and (rationalp b) (equal (/ (* 3 b)) 1))
            (<= 1 b))
   :rule-classes nil))

; The same defect through an ordinary coefficient.
(must-fail
 (defthm bogus-2x
   (implies (and (rationalp x) (equal (/ (* 2 x)) 1))
            (<= 1 x))
   :rule-classes nil))

; CONTROL 1: the shapes invert-var handles correctly must stay sound AND the
; reciprocal reasoning must still work -- a true theorem through the same path.
(defthm honest-reciprocal
  (implies (and (rationalp b) (equal (/ b) 1))
           (<= 1 b))
  :rule-classes nil)

; CONTROL 2: with non-linear arithmetic off, the bogus conjecture is refused
; whatever happens to invert-var -- this pins that the route is the non-linear
; one and not something else.
(must-fail
 (defthm bogus-needs-nonlinear
   (implies (and (rationalp b) (equal (/ (* 3 b)) 1))
            (<= 1 b))
   :hints (("Goal" :nonlinearp nil))
   :rule-classes nil))
