; 02-roots-of-unity.lisp
;
; Introduces the three cube roots of unity e^{j n gamma},
; gamma = 2*pi/3, n=0,1,2 -- used in equations (16)-(28) and in the
; three-phase collapse lemma (33)-(35) -- and proves that their sum
; is zero (paper images 20 and 58-60).
;
; HONESTY BOUNDARY: sqrt(3) is irrational. Standard ACL2 (without
; ACL2(r)) only has rational and complex-rational numbers as objects:
; there is NO rational ACL2 object that satisfies s3*s3=3, so
; introducing s3 via ENCAPSULATE (which requires exhibiting a
; concrete witness) is impossible here. Instead, s3 is left as a
; universally quantified free variable in every theorem, with the
; explicit hypothesis (equal (* s3 s3) 3). This is honest and
; sufficient: every theorem says "for any s3 satisfying s3^2=3 (in
; particular, sqrt(3), if one were working over the reals), the
; following holds".

(in-package "ACL2")
(include-book "00-complex-vectors")

(defun e0 () (declare (xargs :guard t)) (cplx 1 0))
(defun e1 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (/ s3 2)))
(defun e2 (s3)
  (declare (xargs :guard (acl2-numberp s3)))
  (cplx (- (/ 1 2)) (- (/ s3 2))))

; --- Image 20: 1 + e^{j gamma} + e^{j 2 gamma} = 0 ---
(defthm eq-roots-of-unity-sum-zero
  (equal (cadd (e0) (cadd (e1 s3) (e2 s3)))
         (cplx 0 0)))

; --- Image 60: the sum of cube roots with the doubled angle (used in
;     the collapse lemma, applied to the mutual term) is also zero.
;     It is the SAME sum as above, only the n=0,1,2 terms land in a
;     different order (0, 4pi/3, 8pi/3 = 2pi/3): e0 + e2 + e1. ---
(defthm eq-roots-of-unity-double-angle-sum-zero
  (equal (cadd (e0) (cadd (e2 s3) (e1 s3)))
         (cplx 0 0)))
