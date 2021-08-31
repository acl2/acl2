; Specification of the gadget in [ZPS:A.3.3.3].

(in-package "ZCASH")

(include-book "a-3-3-1-spec")

(include-book "kestrel/crypto/ecurve/birational-montgomery-twisted-edwards" :dir :system)

(define edwards-montgomery-precond (u v)
  :guard (and (fep u (jubjub-q))
              (fep v (jubjub-q)))
  (and (affine-edwards-spec u v)
       (not (equal u 0))
       (not (equal v 1))))

(defconst *edwards-montgomery-scaling*
  ;; positive square root of -40964
  17814886934372412843466061268024708274627479829237077604635722030778476050649)

(defrule fep-of-*edwards-montgomery-scaling*
  (fep *edwards-montgomery-scaling* (jubjub-q))
  :enable (fep jubjub-q))

(define edwards-montgomery-spec (u v x y)
  :guard (and (fep u (jubjub-q))
              (fep v (jubjub-q))
              (fep x (jubjub-q))
              (fep y (jubjub-q))
              (edwards-montgomery-precond u v))
  (b* ((epoint (ecurve::point-finite u v))
       (mpoint (ecurve::point-finite x y)))
    (equal (ecurve::twisted-edwards-point-to-montgomery-point
            epoint (jubjub-curve) *edwards-montgomery-scaling*)
           mpoint))
  :guard-hints (("Goal" :in-theory (enable edwards-montgomery-precond
                                           affine-edwards-spec
                                           point-on-jubjub-p
                                           (:e ecurve::twisted-edwards-curve->p)
                                           (:e jubjub-curve)
                                           (:e jubjub-q)))))

; we may also need a version of this specification in which
; Montgomery and twisted Edwards are swapped;
; the two specifications may be used for different instances of the gadget
