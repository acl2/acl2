; 00-sampling-function.lisp
;
; The sampling function Sa(x) = sin(x)/x (paper's eq. (1)) and its
; exact value at every argument used by the master equations (7)-(8)
; when instantiated at the topologies worked in the paper: pi/6, pi/3,
; 2pi/3, pi/2 and pi.
;
; Source: P. O. Cayuela, "Deduccion y Verificacion de las Ecuaciones de
; Comportamiento de Rectificadores No Controlados, Semicontrolados y
; Controlados en Configuraciones Multifasicas" (Congreso Parana, 2026),
; and its companion roadmap "Towards Mechanized Verification of
; q-Pulse Rectifier Voltage Equations in ACL2(r)" (submitted to ACL2
; Workshop 2026), whose Section 5 sketched this development in
; pseudocode but never submitted it to the theorem prover.

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "arithmetic-5/top" :dir :system)
(include-book "nonstd/nsa/trig" :dir :system)

; GUARDS NOT VERIFIABLE for SA below: it calls ACL2-SINE from
; nonstd/nsa/trig, whose own guards are unverified in the library (it is
; defined through ACL2(r)'s standard-part machinery), and ACL2 refuses
; to verify the guards of any function whose body calls one. SA is a
; logical definition used only in proofs.
; --- Eq. (1): Sa(x) = sin(x)/x, with the standard Sa(0) = 1 convention.
(defun sa (x) (if (equal x 0) 1 (/ (acl2-sine x) x)))

; sin(2pi/3), needed for the midpoint/bridge comparison below and for
; the semiconverter continuity check in 02-semiconverter-cross-checks.
; Not in nonstd/nsa/trig.lisp directly; derived from sin(pi-x)=sin(x).
(defthm sine-2pi/3
  (equal (acl2-sine (* 2/3 (acl2-pi))) (/ (acl2-sqrt 3) 2))
  :hints (("Goal" :use ((:instance sin-pi-x (x (* 1/3 (acl2-pi))))
                         sine-pi/3
                         (:instance (:theorem (equal (* 2/3 (acl2-pi))
                                                      (+ (acl2-pi) (- (* 1/3 (acl2-pi))))))))
                  :in-theory nil)))

; cos(2pi/3), needed for the Table-IV consistency check in
; 01-topology-instantiation.lisp.
(defthm cosine-2pi/3
  (equal (acl2-cosine (* 2/3 (acl2-pi))) -1/2)
  :hints (("Goal" :use (cosine-pi/3
                         (:instance cos-pi-x (x (* 1/3 (acl2-pi))))
                         (:instance (:theorem (equal (* 2/3 (acl2-pi))
                                                      (+ (acl2-pi) (- (* 1/3 (acl2-pi))))))))
                  :in-theory nil)))

; --- Sa(pi/3): feeds the 3-phase midpoint VCC coefficient, eq. (10),
; and (via a DIFFERENT argument than Sa(2pi/3) below) the 3-phase
; bridge VRMS coefficient, eq. (13).
(defthm sa-pi/3
  (equal (* (sa (* 1/3 (acl2-pi))) 2 (acl2-pi))
         (* 3 (acl2-sqrt 3)))
  :hints (("Goal" :use (sine-pi/3 pi-between-2-4)
                  :in-theory (enable sa))))

; --- Sa(2pi/3): feeds the 3-phase midpoint VRMS coefficient, eq. (11).
(defthm sa-2pi/3
  (equal (* (sa (* 2/3 (acl2-pi))) 4 (acl2-pi))
         (* 3 (acl2-sqrt 3)))
  :hints (("Goal" :use (sine-2pi/3 pi-between-2-4)
                  :in-theory (enable sa))))

; --- Sa(pi/6): feeds the 3-phase bridge VCC coefficient, eq. (12).
(defthm sa-pi/6
  (equal (* (sa (* 1/6 (acl2-pi))) (acl2-pi)) 3)
  :hints (("Goal" :use (sine-pi/6 pi-between-2-4)
                  :in-theory (enable sa))))

; --- Sa(pi/2): feeds the VCC coefficient shared by the single-phase
; full-wave row of Table 1 (bridge family, q=1) and a two-phase
; midpoint rectifier (midpoint family, q=2) -- see the "bifasico"
; theorem in 01-topology-instantiation.lisp.
(defthm sa-pi/2
  (equal (* (sa (* 1/2 (acl2-pi))) (acl2-pi)) 2)
  :hints (("Goal" :use (sine-pi/2 pi-between-2-4)
                  :in-theory (enable sa))))

; --- Sa(pi) = 0: feeds the VRMS coefficient shared by the same two
; families above, and is the crux of the Table 1 (q=1) inconsistency
; documented in 01-topology-instantiation.lisp.
(defthm sa-pi-val
  (equal (sa (acl2-pi)) 0)
  :hints (("Goal" :use (sine-pi)
                  :in-theory (enable sa))))
