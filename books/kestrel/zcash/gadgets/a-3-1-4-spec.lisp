; Specification of the gadget in [ZPS:A.3.1.4].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define nonzero-spec (a)
  :guard (fep a (jubjub-q))
  (not (equal a 0)))
