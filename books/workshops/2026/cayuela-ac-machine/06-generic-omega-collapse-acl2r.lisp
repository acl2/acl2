; 06-generic-omega-collapse-acl2r.lisp
;
; ACL2(r)-ONLY BOOK. Discharges 06-generic-omega-collapse.lisp's
; conditional hypothesis for the real cube root of unity
; omega=e^{j2pi/3}: plain ACL2 has no rational pair satisfying
; omega^2+omega+1=0 (its roots are non-real), so exhibiting a witness
; requires ACL2(r)'s acl2-cosine/acl2-sine. cos(2pi/3) and sin(2pi/3)
; are obtained in closed form by applying the angle-addition formula
; (cosine-of-sums/sine-of-sums) at pi/3+pi/3, using the exact values
; cosine-pi/3=1/2, sine-pi/3=sqrt(3)/2 that nonstd/nsa/trig already
; provides -- this avoids relying on 2pi-periodicity.
;
; This book is self-contained: it does not include-book
; 06-generic-omega-collapse.lisp, since nonstd/nsa/trig can only be
; certified under the ACL2(r) executable and mixing the two images is
; not permitted (see the note in top-acl2r.lisp). It re-declares the
; generic TRINARY-COLLAPSE-LEMMA locally, ported from rationalp to
; realp, so that this file can be certified on its own.
;
; Certify with: ACL2=/path/to/saved_acl2r cert.pl --acl2 "$ACL2" top-acl2r

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "arithmetic-5/top" :dir :system)

; Guards: CPLXP (both components ACL2 numbers) is the domain of the pair
; algebra; RE/IM only need a cons so REALPAIRP can apply to any object.
(defun cplxp (u)
  (declare (xargs :guard t))
  (and (consp u) (acl2-numberp (car u)) (acl2-numberp (cdr u))))
(defun re (u) (declare (xargs :guard (consp u))) (car u))
(defun im (u) (declare (xargs :guard (consp u))) (cdr u))
(defun cplx (a b)
  (declare (xargs :guard (and (acl2-numberp a) (acl2-numberp b))))
  (cons a b))

(defun realpairp (u)
  (declare (xargs :guard t))
  (and (consp u) (realp (re u)) (realp (im u))))

(defun c+ (u v)
  (declare (xargs :guard (and (cplxp u) (cplxp v))))
  (cplx (+ (re u) (re v)) (+ (im u) (im v))))
(defun c- (u v)
  (declare (xargs :guard (and (cplxp u) (cplxp v))))
  (cplx (- (re u) (re v)) (- (im u) (im v))))
(defun cscale (k u)
  (declare (xargs :guard (and (acl2-numberp k) (cplxp u))))
  (cplx (* k (re u)) (* k (im u))))

(defun c* (u v)
  (declare (xargs :guard (and (cplxp u) (cplxp v))))
  (cplx (- (* (re u) (re v)) (* (im u) (im v)))
        (+ (* (re u) (im v)) (* (im u) (re v)))))

(defun vdot (u v)
  (declare (xargs :guard (and (cplxp u) (cplxp v))))
  (+ (* (re u) (re v)) (* (im u) (im v))))

; --- The generic collapse lemma, ported to realp (identical in
; structure to 06-generic-omega-collapse.lisp's rationalp version).
; Guards of OMEGA-POW are verified in a second step: the recursive call's
; guard needs the result to be a CPLXP, proved by induction first.
(defun omega-pow (omega n)
  (declare (xargs :guard (and (cplxp omega) (natp n))
                  :verify-guards nil))
  (if (zp n) (cplx 1 0) (c* omega (omega-pow omega (1- n)))))

(defthm cplxp-of-omega-pow
  (implies (cplxp omega) (cplxp (omega-pow omega n))))

(verify-guards omega-pow)

(defun collapse-sum (A omega)
  (declare (xargs :guard (and (cplxp A) (cplxp omega))))
  (c+ (cscale (* 2/3 (vdot A (omega-pow omega 0))) (omega-pow omega 0))
      (c+ (cscale (* 2/3 (vdot A (omega-pow omega 1))) (omega-pow omega 1))
          (cscale (* 2/3 (vdot A (omega-pow omega 2))) (omega-pow omega 2)))))

(defthm real-square->=-0
  (implies (realp a) (>= (* a a) 0))
  :rule-classes :linear
  :hints (("Goal" :cases ((<= a 0)))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t)))

; Degenerate branch: if omega were purely real (its imaginary part 0),
; the cubic reduces to (car omega)^2+(car omega)+1=0 for real
; (car omega), which has no real solution (negative discriminant).
; This lemma rules that branch out by contradiction.
(defthm quadratic-always-positive
  (implies (realp x) (> (+ (* x x) x 1) 0))
  :hints (("Goal" :use ((:instance real-square->=-0 (a (+ x 1/2))))
                  :nonlinearp t)))

(defthm expt-b-3-reduction
  (implies (and (realp b) (equal (expt b 2) 3/4))
           (equal (expt b 3) (* b 3/4)))
  :hints (("Goal" :nonlinearp t)))

(defthm expt-b-4-reduction
  (implies (and (realp b) (equal (expt b 2) 3/4))
           (equal (expt b 4) 9/16))
  :hints (("Goal" :nonlinearp t)))

(defthm trinary-collapse-lemma
  (implies (and (realpairp A) (realpairp omega)
                (equal (c+ (cplx 1 0) (c+ omega (c* omega omega)))
                       (cplx 0 0)))
           (equal (collapse-sum A omega) A))
  :hints (("Goal"
           :in-theory (enable omega-pow c+ c* cscale vdot re im cplx realpairp)
           :use ((:instance quadratic-always-positive (x (car omega)))))
          ("Subgoal 2" :nonlinearp t)
          ("Subgoal 1" :nonlinearp t)))

; =============================================================================
; Concrete construction of omega = e^{j 2pi/3}.
; =============================================================================

(defthm sqrt-3-squared
  (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3)
  :hints (("Goal" :use (:instance sqrt-=-y (x 3) (y (acl2-sqrt 3))))))

; Bridge (* x x) <-> (expt x 2): needed because arithmetic-5 normalizes
; squares to expt form. Disabled immediately after use to avoid a
; rewrite loop against arithmetic-5's own normalization rule.
(defthm expt-2-is-times
  (implies (acl2-numberp x) (equal (expt x 2) (* x x))))
(in-theory (disable expt-2-is-times))

(defthm sqrt-3-squared-expt
  (equal (expt (acl2-sqrt 3) 2) 3)
  :hints (("Goal" :use ((:instance expt-2-is-times (x (acl2-sqrt 3)))
                        sqrt-3-squared))))

; GUARDS NOT VERIFIABLE for the functions below that call ACL2-PI /
; ACL2-SINE / ACL2-COSINE / ACL2-SQRT: those library functions (nonstd/
; nsa/trig) have unverified guards, and ACL2 refuses to verify guards of
; any function whose body calls one.
(defun gamma-val () (+ (* 1/3 (acl2-pi)) (* 1/3 (acl2-pi))))

(defthm cos-gamma-val
  (equal (acl2-cosine (gamma-val)) -1/2)
  :hints (("Goal" :in-theory (enable gamma-val)
           :use ((:instance cosine-of-sums (x (* 1/3 (acl2-pi))) (y (* 1/3 (acl2-pi))))
                 cosine-pi/3 sine-pi/3 sqrt-3-squared-expt))))

(defthm sin-gamma-val
  (equal (acl2-sine (gamma-val)) (/ (acl2-sqrt 3) 2))
  :hints (("Goal" :in-theory (enable gamma-val)
           :use ((:instance sine-of-sums (x (* 1/3 (acl2-pi))) (y (* 1/3 (acl2-pi))))
                 cosine-pi/3 sine-pi/3))))

(defun omega-real () (cplx (acl2-cosine (gamma-val)) (acl2-sine (gamma-val))))

(defthm omega-real-closed-form
  (equal (omega-real) (cplx -1/2 (/ (acl2-sqrt 3) 2)))
  :hints (("Goal" :in-theory (enable omega-real)
           :use (cos-gamma-val sin-gamma-val))))

; omega^2+omega+1=0, by direct algebraic substitution of the closed
; form (no need to go through "omega^3=1 and omega!=1" here, since the
; exact value lets the quadratic be checked immediately).
(defthm omega-real-satisfies-cubic
  (equal (c+ (cplx 1 0) (c+ (omega-real) (c* (omega-real) (omega-real))))
         (cplx 0 0))
  :hints (("Goal" :in-theory (enable c+ c* cplx)
           :use (omega-real-closed-form sqrt-3-squared-expt))))

(defthm realpairp-omega-real
  (realpairp (omega-real))
  :hints (("Goal" :in-theory (enable omega-real))))

; =============================================================================
; FINAL THEOREM: the three-phase collapse lemma for the concrete real
; omega=e^{j2pi/3} -- now UNCONDITIONAL. An independent confirmation,
; for an arbitrary vector A, of what 04-collapse-lemma.lisp already
; established directly for the specific roots e0/e1(s3)/e2(s3).
; =============================================================================

(defthm trinary-collapse-CONCRETE
  (implies (realpairp A)
           (equal (collapse-sum A (omega-real)) A))
  :hints (("Goal" :use ((:instance trinary-collapse-lemma
                                   (omega (omega-real)))
                        omega-real-satisfies-cubic
                        realpairp-omega-real)
                  :in-theory (disable trinary-collapse-lemma))))
