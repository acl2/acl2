; 06-generic-omega-collapse.lisp
;
; An independent, more general treatment of the three-phase collapse
; lemma than 04-collapse-lemma.lisp. That book instantiates the three
; concrete cube roots e0, e1(s3), e2(s3) directly and closes the
; resulting polynomial identity by brute nonlinear arithmetic; this
; book instead proves the SAME collapse for an arbitrary complex
; number omega satisfying only the minimal polynomial
; omega^2+omega+1=0 -- a strictly more general statement, established
; via the algebraic argument that a product ring with no zero divisors
; and the factorization x^3-1=(x-1)(x^2+x+1) force this, rather than
; by direct coordinate computation.
;
; Reuses 00-complex-vectors.lisp's pair algebra (cplx/re/imz/cadd/
; csub/cmul/cscale/dotp) rather than re-declaring it, so only a
; RATIONALP-tracking predicate (REALPAIRP, despite the name -- kept to
; match the ACL2(r) companion file's terminology -- means "rational
; pair" here, since this book has no ACL2(r) available) is added.
;
; HONESTY BOUNDARY: plain ACL2 has no rational complex number
; satisfying omega^2+omega+1=0 (its roots are non-real), so the main
; result here, TRINARY-COLLAPSE-LEMMA, is necessarily conditional:
; "if omega satisfies this cubic, then the collapse holds for it."
; This is NOT a dependency of 04-collapse-lemma.lisp's result, which
; already establishes the collapse lemma unconditionally (modulo the
; honest s3*s3=3 hypothesis of 02-roots-of-unity.lisp) by direct
; computation on the concrete roots. 06-generic-omega-collapse-acl2r.lisp
; discharges this book's conditional hypothesis for the real
; omega=e^{j2pi/3}, using ACL2(r) to exhibit a witness plain ACL2
; cannot.

(in-package "ACL2")
(include-book "00-complex-vectors")

(defun realpairp (u)
  (declare (xargs :guard t))
  (and (consp u) (rationalp (re u)) (rationalp (imz u))))

; --- No zero divisors for rational pairs under cmul, established via
; a pair of polynomial identities rather than a general ring argument.
(defthm rational-square->=-0
  (implies (rationalp a) (>= (* a a) 0))
  :rule-classes :linear
  :hints (("Goal" :cases ((<= a 0)))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t)))

(defthm sum-sq-zero-forward
  (implies (and (rationalp a) (rationalp b) (equal (+ (* a a) (* b b)) 0))
           (and (equal a 0) (equal b 0)))
  :rule-classes nil
  :hints (("Goal" :use (rational-square->=-0
                        (:instance rational-square->=-0 (a b))))))

(defthm sum-of-squares-zero-iff-both-zero
  (implies (and (rationalp a) (rationalp b))
           (iff (equal (+ (* a a) (* b b)) 0)
                (and (equal a 0) (equal b 0))))
  :hints (("Goal" :use sum-sq-zero-forward)))

; Pure polynomial identities (not going through cmul/realpairp) that
; certify the key "no zero divisors" step: with u=(a,b), v=(c,d),
;   a*(ac-bd) + b*(ad+bc) =  c*(a^2+b^2)
;   b*(ac-bd) - a*(ad+bc) = -d*(a^2+b^2)
(defthm poly-identity-re
  (implies (and (rationalp a)(rationalp b)(rationalp c)(rationalp d))
           (equal (+ (* a (- (* a c)(* b d))) (* b (+ (* a d)(* b c))))
                  (* c (+ (* a a)(* b b))))))

(defthm poly-identity-im
  (implies (and (rationalp a)(rationalp b)(rationalp c)(rationalp d))
           (equal (- (* b (- (* a c)(* b d))) (* a (+ (* a d)(* b c))))
                  (- (* d (+ (* a a)(* b b)))))))

(defthm key-consequence-re
  (implies (and (rationalp a)(rationalp b)(rationalp c)(rationalp d)
                (equal (* a c) (* b d))
                (equal (+ (* a d) (* b c)) 0))
           (equal (* c (+ (* a a) (* b b))) 0))
  :hints (("Goal" :use (:instance poly-identity-re))))

(defthm key-consequence-im
  (implies (and (rationalp a)(rationalp b)(rationalp c)(rationalp d)
                (equal (* a c) (* b d))
                (equal (+ (* a d) (* b c)) 0))
           (equal (* d (+ (* a a) (* b b))) 0))
  :hints (("Goal" :use (:instance poly-identity-im))))

(defthm c-and-d-are-zero
  (implies (and (rationalp a)(rationalp b)(rationalp c)(rationalp d)
                (equal (* a c) (* b d))
                (equal (+ (* a d) (* b c)) 0)
                (not (and (equal a 0) (equal b 0))))
           (and (equal c 0) (equal d 0)))
  :rule-classes nil
  :hints (("Goal" :use (key-consequence-re key-consequence-im
                        (:instance sum-of-squares-zero-iff-both-zero)))))

(defthm cmul-no-zero-divisors
  (implies (and (realpairp u) (realpairp v)
                (equal (cmul u v) (cplx 0 0))
                (not (equal u (cplx 0 0))))
           (equal v (cplx 0 0)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable cmul realpairp)
           :use (:instance c-and-d-are-zero
                            (a (car u)) (b (cdr u)) (c (car v)) (d (cdr v))))))

; From omega^3=1, omega!=1, the minimal polynomial omega^2+omega+1=0
; follows via the factorization x^3-1=(x-1)(x^2+x+1) in an integral
; domain (no zero divisors).
(defthm cube-root-of-unity-implies-minimal-polynomial
  (implies (and (realpairp omega)
                (equal (cmul omega (cmul omega omega)) (cplx 1 0))
                (not (equal omega (cplx 1 0))))
           (equal (cadd (cplx 1 0) (cadd omega (cmul omega omega)))
                  (cplx 0 0)))
  :hints (("Goal"
           :use (:instance cmul-no-zero-divisors
                            (u (csub omega (cplx 1 0)))
                            (v (cadd (cplx 1 0) (cadd omega (cmul omega omega)))))
           :in-theory (enable cmul csub cadd cplx re imz realpairp))))

; --- The generic collapse lemma: for any omega satisfying its minimal
; polynomial, sum_{n=0}^{2} (2/3)(A . omega^n) omega^n = A.
; Guards are verified in a second step: the recursive call's guard
; needs OMEGA-POW to return a CPLXP, which is itself proved by
; induction over the (still unverified-guard) definition.
(defun omega-pow (omega n)
  (declare (xargs :guard (and (cplxp omega) (natp n))
                  :verify-guards nil))
  (if (zp n) (cplx 1 0) (cmul omega (omega-pow omega (1- n)))))

(defthm cplxp-of-omega-pow
  (implies (cplxp omega) (cplxp (omega-pow omega n))))

(verify-guards omega-pow)

(defun collapse-sum (A omega)
  (declare (xargs :guard (and (cplxp A) (cplxp omega))))
  (cadd (cscale (* 2/3 (dotp A (omega-pow omega 0))) (omega-pow omega 0))
      (cadd (cscale (* 2/3 (dotp A (omega-pow omega 1))) (omega-pow omega 1))
          (cscale (* 2/3 (dotp A (omega-pow omega 2))) (omega-pow omega 2)))))

; Auxiliary reductions: once ACL2 derives (car omega)=-1/2 and
; (cdr omega)^2=3/4 from the cubic, it needs help reducing the 3rd and
; 4th powers of (cdr omega) to that base.
(defthm expt-b-3-reduction
  (implies (and (rationalp b) (equal (expt b 2) 3/4))
           (equal (expt b 3) (* b 3/4)))
  :hints (("Goal" :nonlinearp t)))

(defthm expt-b-4-reduction
  (implies (and (rationalp b) (equal (expt b 2) 3/4))
           (equal (expt b 4) 9/16))
  :hints (("Goal" :nonlinearp t)))

; Degenerate branch: if omega were purely rational (its imaginary part
; 0), the cubic reduces to (car omega)^2+(car omega)+1=0 for rational
; (car omega), which has no rational solution (negative discriminant).
; This lemma rules that branch out by contradiction.
(defthm quadratic-always-positive-rational
  (implies (rationalp x) (> (+ (* x x) x 1) 0))
  :hints (("Goal" :use ((:instance rational-square->=-0 (a (+ x 1/2))))
                  :nonlinearp t)))

(defthm trinary-collapse-lemma
  (implies (and (realpairp A) (realpairp omega)
                (equal (cadd (cplx 1 0) (cadd omega (cmul omega omega)))
                       (cplx 0 0)))
           (equal (collapse-sum A omega) A))
  :hints (("Goal"
           :in-theory (enable omega-pow cadd cmul cscale dotp re imz cplx realpairp)
           :use ((:instance quadratic-always-positive-rational (x (car omega)))))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t)))
