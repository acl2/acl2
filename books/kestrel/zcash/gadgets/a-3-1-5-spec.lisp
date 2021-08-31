; Specification of the gadget in [ZPS:A.3.1.4].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define xor-precond (a b)
  :guard (and (fep a (jubjub-q)) (fep b (jubjub-q)))
  (and (bitp a) (bitp b)))

(define xor-spec (a b c)
  :guard (and (fep a (jubjub-q))
              (fep b (jubjub-q))
              (fep c (jubjub-q))
              (xor-precond a b))
  (equal c (if (equal a b) 0 1)))
