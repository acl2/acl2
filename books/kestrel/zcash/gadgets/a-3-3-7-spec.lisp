; Specification of the gadget in [ZPS:A.3.3.7].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define fixed-edwards-mul-spec (k b u v)
  :guard (and (fep k (jubjub-q))
              (jubjub-pointp b)
              (fep u (jubjub-q))
              (fep v (jubjub-q)))
  (equal (ecurve::twisted-edwards-mul k b (jubjub-curve))
         (ecurve::point-finite u v))
  :guard-hints (("Goal" :in-theory (enable jubjub-pointp
                                           point-on-jubjub-p))))

; use instances (fixed-edwards-mul-spec k b u v)
; for constant points b
