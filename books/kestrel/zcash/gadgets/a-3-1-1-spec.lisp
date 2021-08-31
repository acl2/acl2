; Specification of the gadget in [ZPS:A.3.1.1].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define boolean-spec (b)
  :guard (fep b (jubjub-q))
  (bitp b))
