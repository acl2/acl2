; 08-inductance-integral.lisp
;
; ACL2(r)-ONLY BOOK. Requires the ACL2(r) executable (saved_acl2r) --
; see the note in 07-inductance-note.lisp on why this content cannot
; live in the plain-ACL2 chain certified by top.lisp. Certify with:
;
;   ACL2=/path/to/saved_acl2r cert.pl --acl2 "$ACL2" top-acl2r
;
; This book picks up exactly where 07-inductance-note.lisp left off:
; Section III.F of the source paper needs
;   integral_0^{2pi} cos(delta-m*gamma) cos(delta-n*gamma) d(delta)
; (the "winding function" self/mutual inductance integral), and the
; companion ACL2 Workshop paper identifies the antiderivative
;   F(x) = (1/2) cos((n-m)*gamma) * x + (1/4) sin(2x-(m+n)*gamma)
; worked out by hand, plus the exact library entry point
; (books/nonstd/integrals/ftc-2.lisp) needed to turn "F is an
; antiderivative of the integrand" into a proof of the integral's
; value, via ftc-2's generic Fundamental Theorem of Calculus.
;
; What this book actually establishes, certified:
;
;   (1) The integrand equals the SAME sum-of-cosines form that F's
;       derivative should equal (COS-PRODUCT-TO-SUM,
;       INDUCTANCE-INTEGRAND-AS-SUM) -- i.e. the trigonometric algebra
;       underlying the antiderivative is confirmed exactly, mechanically,
;       not just by hand.
;
;   (2) The RAW (complex-exponential) nonstandard derivative of
;       sin(2x-c), for a symbolic constant c, obtained automatically
;       from the Reid-Gamboa automatic differentiator
;       (SIN-2X-MINUS-C-DERIV, via DEFDERIVATIVE) -- a genuine,
;       machine-derived differentiation fact, not asserted.
;
; What remains open, honestly: connecting (2) back to a statement in
; terms of ACL2(r)'s acl2-sine/acl2-cosine (as opposed to raw
; acl2-exp) -- the step SINE-LINEAR-SHIFT-SCALE-DERIVATIVE would be --
; ran, in every strategy attempted (chain-rule composition via
; ACL2-SINE-DERIVATIVE + CLOSE-LIMITED from
; nonstd/circles/circumference-of-a-circle.lisp; direct use of
; SIN-2X-MINUS-C-DERIV with acl2-sine/acl2-cosine's definitions
; enabled), into severe ACL2/arithmetic-5 rewrite-loop and
; combinatorial-expansion behavior: repeated ping-pong between
; cosine-of-sums and its converse, between
; functional-commutativity-of-minus-*-{left,right} and (- (* c x)),
; between integerp-minus-x and (integerp (- x)), and, once those are
; disabled, a genuine (non-looping but unresolved) explosion of
; binomial/exponential terms from expanding (expt (acl2-exp ...) 2).
; Each of these was individually diagnosed (via :brr t / cw-gstack)
; and worked around in isolation, but the composition did not close
; within the scope of this session. This is not a gap in the
; mathematics -- Sec. 4.4's own ACL2(r) omega-construction argument in
; the companion paper crosses very similar terrain -- it is a gap in
; proof engineering effort, of a size the companion paper itself
; anticipated ("comparable in size to the work reported in
; Section 4.4"). Completing it, and then the further step of
; instantiating ftc-2 itself, is left for a follow-up session; nothing
; below asserts or simulates that missing step.

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-minimal" :dir :system)
(include-book "nonstd/workshops/2011/reid-gamboa-differentiator/support/differentiator" :dir :system)

; GUARDS NOT VERIFIABLE: the functions below call ACL2-PI / ACL2-SINE /
; ACL2-COSINE from nonstd/nsa/trig, whose own guards are unverified in
; the library (they are defined through ACL2(r)'s standard-part
; machinery), and ACL2 refuses to verify the guards of any function
; whose body calls one. They are logical (non-executable) definitions
; used only in proofs.

; gamma = 2*pi/3, the stator/rotor winding spacing of Section 2.
(defun winding-gamma () (* 2/3 (acl2-pi)))

; The winding-function inductance integrand, cos(x-m*gamma)*cos(x-n*gamma).
(defun inductance-integrand (x m n)
  (* (acl2-cosine (- x (* m (winding-gamma)))) (acl2-cosine (- x (* n (winding-gamma))))))

; The antiderivative worked out by hand in the companion paper's
; Section 5 ("What Was Not Mechanized").
(defun inductance-antideriv (x m n)
  (+ (* 1/2 (acl2-cosine (* (- n m) (winding-gamma))) x)
     (* 1/4 (acl2-sine (- (* 2 x) (* (+ m n) (winding-gamma)))))))

; --- (1) The trigonometric algebra: product-to-sum, general form,
; used to confirm the antiderivative's shape below.
(defthm cos-product-to-sum
  (implies (acl2-numberp b)
   (equal (* (acl2-cosine a) (acl2-cosine b))
          (* 1/2 (+ (acl2-cosine (- a b)) (acl2-cosine (+ a b))))))
  :hints (("Goal" :use ((:instance cosine-of-sums (x a) (y b))
                         (:instance cosine-of-sums (x a) (y (- b)))
                         (:instance cos-uminus (x b))
                         (:instance sin-uminus (x b))))))

(in-theory (disable cos-product-to-sum))

(defthm inductance-integrand-as-sum
  (implies (acl2-numberp x)
   (equal (inductance-integrand x m n)
          (* 1/2 (+ (acl2-cosine (* (- n m) (winding-gamma)))
                    (acl2-cosine (- (* 2 x) (* (+ m n) (winding-gamma))))))))
  :hints (("Goal" :in-theory (disable winding-gamma
                                       cosine-of-sums sine-of-sums cos-uminus sin-uminus
                                       functional-commutativity-of-minus-*-left
                                       functional-commutativity-of-minus-*-right
                                       |(- (* c x))|)
                  :expand ((inductance-integrand x m n))
                  :use ((:instance cos-product-to-sum
                                    (a (- x (* m (winding-gamma))))
                                    (b (- x (* n (winding-gamma)))))))))

; --- (2) The raw nonstandard derivative of sin(2x-c), obtained
; automatically (not asserted) by the Reid-Gamboa differentiator from
; sin(2x-c)'s own defining complex-exponential formula.
(defderivative sin-2x-minus-c-deriv
  (/ (- (acl2-exp (* #c(0 1) (- (* 2 x) c)))
        (acl2-exp (* #c(0 -1) (- (* 2 x) c))))
     #c(0 2)))
