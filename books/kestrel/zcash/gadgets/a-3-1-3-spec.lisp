; Specification of the gadget in [ZPS:A.3.1.3].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define selection-precond (b)
  :guard (fep b (jubjub-q))
  (bitp b))

(define selection-spec (b x y z)
  :guard (and (fep b (jubjub-q))
              (fep x (jubjub-q))
              (fep y (jubjub-q))
              (fep z (jubjub-q))
              (selection-precond b))
  (equal z (if (equal b 1) x y)))
