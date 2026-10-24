; 01-euler-identities.lisp
;
; Verifies equations (10)-(12) of the paper: Euler's identities and
; their relation to the dot product.
;
; HONESTY BOUNDARY: ACL2 (without the ACL2(r) nonstandard-analysis
; extension) has no theory of transcendental functions or real
; analysis: it cannot "derive" sine and cosine from first principles.
; For that reason, cosine/sine are introduced here via ENCAPSULATE as
; functions CONSTRAINED to satisfy a set of standard trigonometric
; facts (Pythagorean identity, parity, angle-difference formulas)
; that are IMPORTED as axioms, not proved. The local witness used to
; admit the encapsulate is the trivial constant function
; (cosine=1, sine=0), which happens to satisfy every constraint; this
; only shows the constraints are consistent, not that cosine/sine are
; the real trigonometric functions. Everything proved AFTER this
; point should therefore be read as: "for any pair of functions
; satisfying these standard properties of sine and cosine, the
; following holds...".

(in-package "ACL2")
(include-book "00-complex-vectors")

(encapsulate
 (((cosine *) => *) ((sine *) => *))
 (local (defun cosine (x) (declare (ignore x)) 1))
 (local (defun sine (x) (declare (ignore x)) 0))
 (defthm pythagorean-cos-sin
   (equal (+ (* (cosine x) (cosine x)) (* (sine x) (sine x))) 1))
 (defthm cosine-even
   (equal (cosine (- x)) (cosine x)))
 (defthm sine-odd
   (equal (sine (- x)) (- (sine x))))
 (defthm cosine-difference
   (equal (cosine (- x y))
          (+ (* (cosine x) (cosine y)) (* (sine x) (sine y)))))
 (defthm sine-difference
   (equal (sine (- x y))
          (- (* (sine x) (cosine y)) (* (cosine x) (sine y)))))
 (defthm acl2-numberp-cosine (acl2-numberp (cosine x)))
 (defthm acl2-numberp-sine (acl2-numberp (sine x))))

; e^{j theta} := cplx(cos theta, sin theta)
(defun eiz (theta)
  (declare (xargs :guard t))
  (cplx (cosine theta) (sine theta)))

; --- Equation (10): cos(delta) = (e^{j delta} + e^{-j delta}) / 2 ---
(defthm eq10-euler-cosine
  (implies (acl2-numberp delta)
           (equal (* 1/2 (+ (re (eiz delta)) (re (eiz (- delta)))))
                  (cosine delta))))

; --- Equation (12): cos(delta - gamma) = e^{j delta} . e^{j gamma} ---
(defthm eq12-cosine-difference-is-dotp
  (implies (and (acl2-numberp delta) (acl2-numberp gamma))
           (equal (dotp (eiz delta) (eiz gamma))
                  (cosine (- delta gamma)))))
