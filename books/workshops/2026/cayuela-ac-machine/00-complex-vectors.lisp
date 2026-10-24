; 00-complex-vectors.lisp
;
; Mechanical verification (ACL2) of the complex<->vector identities
; used in Cayuela, "Modelo vectorial de la maquina de corriente
; alterna trifasica simetrica" ("Vectorial model of the symmetric
; three-phase AC machine"), equations (6)-(9).
;
; Representation: a complex number / 2D vector is represented as
; (cons re im), NOT as ACL2's native complex type (because later on
; irrational/symbolic components appear, such as sqrt(3) and the
; cos/sin of an arbitrary angle, which ACL2's native complex type
; cannot hold: its parts must be rational).
;
; The cross-product convention used here is the paper's own, cited to
; Needham (ref. [2]): A x B := Im(A B*). With A=(a,b), B=(c,d) this
; gives A x B = b*c - a*d, which is the NEGATIVE of the "physics
; textbook" formula a*d - b*c. This is a valid, self-consistent
; convention choice, not an error: it is used consistently throughout
; the rest of the development.

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)

; Guards: a pair is a valid complex/vector value (CPLXP) when both
; components are ACL2 numbers. RE/IMZ only need a cons, so that
; predicates over arbitrary data (e.g. REALPAIRP) can use them.
(defun cplxp (z)
  (declare (xargs :guard t))
  (and (consp z) (acl2-numberp (car z)) (acl2-numberp (cdr z))))
(defun cplx (re im)
  (declare (xargs :guard (and (acl2-numberp re) (acl2-numberp im))))
  (cons re im))
(defun re (z) (declare (xargs :guard (consp z))) (car z))
(defun imz (z) (declare (xargs :guard (consp z))) (cdr z))
(defun cconj (z)
  (declare (xargs :guard (cplxp z)))
  (cplx (re z) (- (imz z))))
(defun cadd (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (+ (re z) (re w)) (+ (imz z) (imz w))))
(defun csub (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (- (re z) (re w)) (- (imz z) (imz w))))
(defun cscale (k z)
  (declare (xargs :guard (and (acl2-numberp k) (cplxp z))))
  (cplx (* k (re z)) (* k (imz z))))
(defun cmul (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (cplx (- (* (re z) (re w)) (* (imz z) (imz w)))
        (+ (* (re z) (imz w)) (* (imz z) (re w)))))
(defun dotp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (+ (* (re z) (re w)) (* (imz z) (imz w))))
(defun crossp (z w)
  (declare (xargs :guard (and (cplxp z) (cplxp w))))
  (- (* (imz z) (re w)) (* (re z) (imz w))))

; --- Equation (6): AB* + A*B = 2 (A . B) ---
(defthm eq6-dot-product-real-part
  (equal (re (cadd (cmul z (cconj w)) (cmul (cconj z) w)))
         (* 2 (dotp z w))))

(defthm eq6-dot-product-imag-part
  (equal (imz (cadd (cmul z (cconj w)) (cmul (cconj z) w)))
         0))

; --- Equations (8)-(9): AB* - A*B = j2 (A x B) ---
(defthm eq8-9-cross-product-real-part
  (equal (re (csub (cmul z (cconj w)) (cmul (cconj z) w)))
         0))

(defthm eq8-9-cross-product-imag-part
  (equal (imz (csub (cmul z (cconj w)) (cmul (cconj z) w)))
         (* 2 (crossp z w))))

; Direct form of (9), reused in 05-torque-sign-correction.lisp:
; Im(AB*) = A x B.
(defthm eq9-im-ab-star-is-crossp
  (equal (imz (cmul z (cconj w)))
         (crossp z w)))
