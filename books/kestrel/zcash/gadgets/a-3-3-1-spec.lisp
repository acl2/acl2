; Specification of the gadget in [ZPS:A.3.3.1].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define affine-edwards-spec (u v)
  :guard (and (fep u (jubjub-q)) (fep v (jubjub-q)))
  (point-on-jubjub-p (ecurve::point-finite u v)))
