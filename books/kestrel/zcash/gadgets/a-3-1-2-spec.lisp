; Specification of the gadget in [ZPS:A.3.1.2].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define condeq-spec (a b c)
  :guard (and (fep a (jubjub-q))
              (fep b (jubjub-q))
              (fep c (jubjub-q)))
  (or (equal a 0)
      (equal b c)))
