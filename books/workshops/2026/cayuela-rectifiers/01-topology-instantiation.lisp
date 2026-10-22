; 01-topology-instantiation.lisp
;
; Instantiates the master equations
;   VCC  = Vm . Sa(T/2) . fAV(alpha)                        (eq. 7)
;   VRMS = VmRMS . sqrt(1 + Sa(T) . fRMS(alpha))             (eq. 8)
; at the topologies worked in the paper, using the exact Sa-values
; proved in 00-sampling-function.lisp, and formalizes two findings
; that came out of this mechanization.

; cert_param: (uses-acl2r)

(in-package "ACL2")
(include-book "00-sampling-function")

; --- Eq. (12): VCC of the 3-phase bridge = sqrt(3)*Vmax*Sa(pi/6)*cos(alpha),
; coefficient sqrt(3)*Sa(pi/6) = 3*sqrt(3)/pi.
(defthm eq12-VCC-bridge-3ph-coefficient
  (equal (* (acl2-sqrt 3) (sa (* 1/6 (acl2-pi))) (acl2-pi))
         (* 3 (acl2-sqrt 3)))
  :hints (("Goal" :use sa-pi/6)))

; --- Confirmed coefficient error (found numerically in Sec. V/4 of the
; two papers; confirmed here exactly): the 3-phase midpoint VRMS
; coefficient (eq. 11, which uses Sa(2pi/3)) and the 3-phase bridge
; VRMS coefficient (eq. 13, which must use Sa(pi/3)) are genuinely
; DIFFERENT values -- not interchangeable, as an earlier draft of
; eq. (13) mistakenly did.
(defthm bridge-vs-midpoint-Sa-differ
  (not (equal (sa (* 1/3 (acl2-pi))) (sa (* 2/3 (acl2-pi)))))
  :hints (("Goal" :use (sa-pi/3 sa-2pi/3 pi-between-2-4
                        (:instance sqrt-sqrt (x 3)))
                  :nonlinearp t)))

; --- The "bifasico" identification: the single-phase full-wave row of
; Table 1 (bridge family, q=1: T=pi/1, Vm=Vmax) and a two-phase
; midpoint rectifier (midpoint family, q=2: T=2pi/2, Vm=Vmax) are the
; SAME instantiation of the master equations, not two topologies that
; happen to agree numerically: they substitute the identical T (and
; the identical Vm=Vmax, per Table I), so Sa-pi/2 and Sa-pi-val below
; are literally shared, not separately re-derived, between the two
; parametrizations.
(defthm bifasico-T-coincides
  (equal (/ (acl2-pi) 1) (/ (* 2 (acl2-pi)) 2)))

; sqrt(1/2) <> 1, used below to show the printed Table-1/IV row for
; q=1 cannot be the value the master equation forces.
(defthm sqrt-1/2-not-1
  (not (equal (acl2-sqrt 1/2) 1))
  :hints (("Goal" :use ((:instance sqrt-sqrt (x 1/2))))))

; --- Table 1 / Table IV inconsistency (a new finding, not present in
; either paper): for the shared (T=pi, Vm=Vmax) family above,
; Sa(T)=Sa(pi)=0 exactly, so master eq. (8) forces VRMS/VmRMS to be
; CONSTANT (=1) for every alpha -- this is in fact the standard,
; slightly non-obvious power-electronics fact that the RMS output of a
; single-phase full converter under continuous conduction does not
; depend on the firing angle. But the printed table entry for that
; row, VRMS/VmRMS = sqrt(1+cos(2*alpha)), is NOT constant: at
; alpha=pi/3 it evaluates to sqrt(1/2) <> 1. The table entry is
; therefore inconsistent with the paper's own master equations.
(defthm q1-table-VRMS-row-inconsistent-with-master-eq
  (and (equal (sa (acl2-pi)) 0)
       (not (equal (acl2-sqrt (+ 1 (acl2-cosine (* 2/3 (acl2-pi))))) 1)))
  :hints (("Goal" :use (sa-pi-val cosine-2pi/3 sqrt-1/2-not-1))))
