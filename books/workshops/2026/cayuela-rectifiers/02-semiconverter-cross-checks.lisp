; 02-semiconverter-cross-checks.lisp
;
; The three cross-checks for the three-phase semi-converter's two-
; regime VRMS (eqs. 15-16 in the Spanish paper, 11-12 in the English
; roadmap), sketched as unproved i-close conjectures in Section 5.3 of
; the ACL2(r) roadmap paper ("semiconv-continuity-at-pi/3",
; "semiconv-limit-alpha-0", "semiconv-limit-alpha-pi") and discharged
; here as EXACT equalities: alpha=pi/3, 0 and pi are standard rational
; points with known exact trig values, so no nonstandard-analysis
; machinery (i-close, standard-part) is actually needed to settle
; these three specific points -- a strictly stronger result than what
; the roadmap sketch asked for.

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "00-sampling-function")

; --- (i) Eqs. (15) and (16) meet exactly at alpha=pi/3: the only term
; that differs between the two branches, sqrt(3)*cos^2(alpha) (eq. 15)
; vs. (1/2)*sin(2*alpha) (eq. 16), is the same value at that point.
(defthm semiconv-continuity-at-pi/3
  (equal (* (acl2-sqrt 3) (expt (acl2-cosine (* 1/3 (acl2-pi))) 2))
         (* 1/2 (acl2-sine (* 2/3 (acl2-pi)))))
  :hints (("Goal" :use (cosine-pi/3 sine-2pi/3))))

; --- (ii) Eq. (15) at alpha=0 reproduces the uncontrolled 3-phase
; bridge, eq. (13): both inner expressions equal 1/2 + 3*sqrt(3)/(4*pi).
(defthm semiconv-alpha-0-matches-bridge
  (equal (* 3 (/ (* 4 (acl2-pi)))
            (+ (* 2/3 (acl2-pi)) (* (acl2-sqrt 3) (expt (acl2-cosine 0) 2))))
         (* 1/2
            (+ 1 (* (/ (* 3 (acl2-sqrt 3)) (* 2 (acl2-pi))) (acl2-cosine 0)))))
  :hints (("Goal" :use (cosine-0 pi-between-2-4))))

; --- (iii) Eq. (16) at alpha=pi gives VRMS=0, consistent with VCC=0 in
; eq. (14): the inner bracket (pi - alpha + (1/2)sin(2*alpha)) vanishes.
(defthm semiconv-alpha-pi-zero
  (equal (+ (- (acl2-pi) (acl2-pi)) (* 1/2 (acl2-sine (* 2 (acl2-pi))))) 0)
  :hints (("Goal" :use (sine-2pi))))
