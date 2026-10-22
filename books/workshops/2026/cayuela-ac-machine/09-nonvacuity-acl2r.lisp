; 09-nonvacuity-acl2r.lisp
;
; ACL2(r)-only. Books 03-05 prove theorems under the hypothesis
; (equal (* s3 s3) 3) (with s3 REALP). In plain ACL2 no ACL2 number
; satisfies it, so there those theorems are schematic. In ACL2(r) the
; hypothesis IS satisfiable, by s3 = (acl2-sqrt 3). This book:
;   1. proves that (acl2-sqrt 3) is real and has square 3, and
;   2. instantiates the theorems of books 03-05 at s3 = (acl2-sqrt 3),
;      obtaining the same statements with NO hypothesis on s3, and
;   3. proves the seven constraints of the ENCAPSULATE of
;      01-euler-identities.lisp for the library's genuinely defined
;      ACL2-COSINE / ACL2-SINE and, by functional instantiation, that
;      the theorems of books 01-05 that mention COSINE/SINE hold for them.

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "nonstd/nsa/trig" :dir :system)
(include-book "arithmetic-5/top" :dir :system)
(include-book "03-zeta-deduction")
(include-book "04-collapse-lemma")
(include-book "05-torque-sign-correction")

(defthm sqrt-3-squared-nv
  (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3)
  :hints (("Goal" :use (:instance sqrt-=-y (x 3) (y (acl2-sqrt 3))))))

(defthm realp-sqrt-3
  (realp (acl2-sqrt 3)))

; The hypotheses on s3 are satisfiable in ACL2(r).
(defthm s3-hypothesis-satisfiable
  (and (realp (acl2-sqrt 3))
       (equal (* (acl2-sqrt 3) (acl2-sqrt 3)) 3))
  :rule-classes nil
  :hints (("Goal" :use (sqrt-3-squared-nv realp-sqrt-3))))

(defthm eq33-35-collapse-concrete
  (implies (and (realp ra) (realp ia))
           (equal (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e0))) (e0))
                  (cadd (cscale (* 2/3 (dotp (cplx ra ia) (e1 (acl2-sqrt 3))))
                                (e1 (acl2-sqrt 3)))
                        (cscale (* 2/3 (dotp (cplx ra ia) (e2 (acl2-sqrt 3))))
                                (e2 (acl2-sqrt 3)))))
                  (cplx ra ia)))
  :hints (("Goal" :use ((:instance eq33-35-three-phase-collapse-lemma
                                   (s3 (acl2-sqrt 3)))
                        sqrt-3-squared-nv realp-sqrt-3))))

(defthm eq-ik-magnitude-squared-concrete
  (implies (and (realp i0) (realp i1) (realp i2)
                (equal i0 (- (+ i1 i2))))
           (equal (+ (* (re (ik i0 i1 i2 (acl2-sqrt 3)))
                        (re (ik i0 i1 i2 (acl2-sqrt 3))))
                     (* (imz (ik i0 i1 i2 (acl2-sqrt 3)))
                        (imz (ik i0 i1 i2 (acl2-sqrt 3)))))
                  (* 9/4 (+ (* i0 i0)
                            (* 1/3 (- i1 i2) (- i1 i2))))))
  :hints (("Goal" :use ((:instance eq-ik-magnitude-squared
                                   (s3 (acl2-sqrt 3)))
                        sqrt-3-squared-nv realp-sqrt-3))))

(defthm sign-matters-concrete
  (not (equal (crossp (cplx 1 1) (cmul (cplx 1 0) (e1 (acl2-sqrt 3))))
              (crossp (cplx 1 1) (cmul (cplx 1 0) (e2 (acl2-sqrt 3))))))
  :hints (("Goal" :use ((:instance sign-matters-nonvacuous
                                   (s3 (acl2-sqrt 3)))
                        sqrt-3-squared-nv realp-sqrt-3))))

; --- The seven constraints of the ENCAPSULATE in 01-euler-identities.lisp
;     (two type facts, Pythagorean identity, parity, angle-difference
;     formulas) hold, with no hypotheses, for the library's genuinely
;     defined ACL2-COSINE / ACL2-SINE. By functional instantiation, the
;     theorems of books 01-05 that mention the abstract COSINE / SINE
;     therefore hold for ACL2-COSINE / ACL2-SINE. ---
(defthm acl2-trig-numberp-cosine (acl2-numberp (acl2-cosine x)))
(defthm acl2-trig-numberp-sine (acl2-numberp (acl2-sine x)))

(defthm acl2-trig-pythagorean
  (equal (+ (* (acl2-cosine x) (acl2-cosine x))
            (* (acl2-sine x) (acl2-sine x)))
         1)
  :hints (("Goal" :use ((:instance cosine-of-sums (x x) (y (- x)))
                        (:instance cos-uminus (x x))
                        (:instance sin-uminus (x x))))))

(defthm acl2-trig-cosine-even
  (equal (acl2-cosine (- x)) (acl2-cosine x)))

(defthm acl2-trig-sine-odd
  (equal (acl2-sine (- x)) (- (acl2-sine x))))

(defthm acl2-trig-cosine-difference
  (equal (acl2-cosine (- x y))
         (+ (* (acl2-cosine x) (acl2-cosine y))
            (* (acl2-sine x) (acl2-sine y)))))

(defthm acl2-trig-sine-difference
  (equal (acl2-sine (- x y))
         (- (* (acl2-sine x) (acl2-cosine y))
            (* (acl2-cosine x) (acl2-sine y)))))

; e^{j theta} and the torque function over the library's functions.
; Guards are not verified: the guards of ACL2-COSINE/ACL2-SINE are not.
(defun eiz-r (theta)
  (declare (xargs :guard t :verify-guards nil))
  (cplx (acl2-cosine theta) (acl2-sine theta)))

(defun torque-w-r (i-s i-r eps)
  (declare (xargs :guard (and (cplxp i-s) (cplxp i-r)) :verify-guards nil))
  (cmul i-s (cconj (cmul i-r (eiz-r eps)))))

(defthm eq10-euler-cosine-r
  (implies (acl2-numberp delta)
           (equal (* 1/2 (+ (re (eiz-r delta)) (re (eiz-r (- delta)))))
                  (acl2-cosine delta)))
  :hints (("Goal" :by (:functional-instance eq10-euler-cosine
                       (cosine acl2-cosine) (sine acl2-sine)
                       (eiz eiz-r)))))

(defthm eq12-cosine-difference-is-dotp-r
  (implies (and (acl2-numberp delta) (acl2-numberp gamma))
           (equal (dotp (eiz-r delta) (eiz-r gamma))
                  (acl2-cosine (- delta gamma))))
  :hints (("Goal" :by (:functional-instance eq12-cosine-difference-is-dotp
                       (cosine acl2-cosine) (sine acl2-sine)
                       (eiz eiz-r)))))

(defthm eq-mutual-phase-shift-r
  (implies (and (real/rationalp p) (real/rationalp q)
                (acl2-numberp x) (acl2-numberp phi))
           (equal (dotp (cplx p q) (eiz-r (- x phi)))
                  (dotp (cmul (cplx p q) (eiz-r phi)) (eiz-r x))))
  :hints (("Goal" :by (:functional-instance eq-mutual-phase-shift
                       (cosine acl2-cosine) (sine acl2-sine)
                       (eiz eiz-r)))))

(defthm eq-W-conjugate-r
  (equal (cconj (torque-w-r i-s i-r eps))
         (cmul (cconj i-s) (cmul i-r (eiz-r eps))))
  :hints (("Goal" :by (:functional-instance eq-W-conjugate
                       (cosine acl2-cosine) (sine acl2-sine)
                       (eiz eiz-r) (torque-w torque-w-r)))))

(defthm eq-im-w-is-crossp-r
  (equal (imz (torque-w-r i-s i-r eps))
         (crossp i-s (cmul i-r (eiz-r eps))))
  :hints (("Goal" :by (:functional-instance eq-im-w-is-crossp
                       (cosine acl2-cosine) (sine acl2-sine)
                       (eiz eiz-r) (torque-w torque-w-r)))))

(defthm torque-exponent-sign-is-plus-r
  (equal (imz (torque-w-r i-s i-r eps))
         (crossp i-s (cmul i-r (eiz-r eps))))
  :rule-classes nil
  :hints (("Goal" :by (:functional-instance torque-exponent-sign-is-plus
                       (cosine acl2-cosine) (sine acl2-sine)
                       (eiz eiz-r) (torque-w torque-w-r)))))
