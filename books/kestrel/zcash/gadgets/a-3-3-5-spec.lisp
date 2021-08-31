; Specification of the gadget in [ZPS:A.3.3.5].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define edwards-add-precond (u1 v1 u2 v2)
  :guard (and (fep u1 (jubjub-q))
              (fep v1 (jubjub-q))
              (fep u2 (jubjub-q))
              (fep v2 (jubjub-q)))
  (and (point-on-jubjub-p (ecurve::point-finite u1 v1))
       (point-on-jubjub-p (ecurve::point-finite u2 v2))))

(define edwards-add-spec (u1 v1 u2 v2 u3 v3)
  :guard (and (fep u1 (jubjub-q))
              (fep v1 (jubjub-q))
              (fep u2 (jubjub-q))
              (fep v2 (jubjub-q))
              (fep u3 (jubjub-q))
              (fep v3 (jubjub-q))
              (edwards-add-precond u1 v1 u2 v2))
  (equal (ecurve::twisted-edwards-add (ecurve::point-finite u1 v1)
                                      (ecurve::point-finite u2 v2)
                                      (jubjub-curve))
         (ecurve::point-finite u3 v3))
  :guard-hints (("Goal" :in-theory (enable edwards-add-precond
                                           point-on-jubjub-p))))
