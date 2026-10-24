; 03-zeta-deduction.lisp
;
; Verifies the algebraic core of the deduction of zeta_k(t), Section
; III.C of the paper (equations 16-28): given the current space
; vector i_k(t) = i_k0 e^{j0} + i_k1 e^{j gamma} + i_k2 e^{j 2 gamma}
; with balanced currents (i_k0+i_k1+i_k2=0), its real and imaginary
; parts and the squared-magnitude formula are proved. atan2 itself is
; not mechanized (transcendental/multivalued); the paper's atan2 rests
; directly on these two algebraic components, which are where a sign
; or factor error could hide.

(in-package "ACL2")
(include-book "02-roots-of-unity")

(defun ik (i0 i1 i2 s3)
  (declare (xargs :guard (and (acl2-numberp i0) (acl2-numberp i1)
                              (acl2-numberp i2) (acl2-numberp s3))))
  (cadd (cscale i0 (e0)) (cadd (cscale i1 (e1 s3)) (cscale i2 (e2 s3)))))

; --- Real part of (16), after applying the current balance (13) ---
(defthm eq16-28-re-ik-balanced
  (implies (equal (+ i0 i1 i2) 0)
           (equal (re (ik i0 i1 i2 s3)) (* 3/2 i0))))

; --- Imaginary part of (16) ---
(defthm eq16-28-imz-ik
  (equal (imz (ik i0 i1 i2 s3)) (* (/ s3 2) (- i1 i2))))

; --- Squared-magnitude formula that feeds the paper's i_k(t)
;     magnitude equation (dividing by sin/cos and summing squares).
;     Requires s3^2=3 and real currents/s3 so ACL2's nonlinear
;     arithmetic can close the goal. REAL/RATIONALP (not RATIONALP) so that
;     the hypotheses are satisfiable in ACL2(r) by s3 = sqrt(3); in
;     plain ACL2 REAL/RATIONALP is RATIONALP and in ACL2(r) it is REALP. ---
(defthm eq-ik-magnitude-squared
  (implies (and (real/rationalp i0) (real/rationalp i1) (real/rationalp i2) (real/rationalp s3)
                (equal i0 (- (+ i1 i2)))
                (equal (* s3 s3) 3))
           (equal (+ (* (re (ik i0 i1 i2 s3)) (re (ik i0 i1 i2 s3)))
                     (* (imz (ik i0 i1 i2 s3)) (imz (ik i0 i1 i2 s3))))
                  (* 9/4 (+ (* i0 i0) (* 1/3 (- i1 i2) (- i1 i2))))))
  :hints (("Goal" :nonlinearp t)))
