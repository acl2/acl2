; Specification of the gadget in [ZPS:A.3.3.9].

(in-package "ZCASH")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/zcash/pedersen-hash" :dir :system)

(define pedersen-precond (ms)
  :guard (pfield::fe-listp ms (jubjub-q))
  (and (bit-listp ms)
       (consp ms)))

(define pedersen-spec (d ms hs)
  :guard (and (byte-listp d)
              (equal (len d) 8)
              (pfield::fe-listp ms (jubjub-q))
              (pfield::fe-listp hs (jubjub-q))
              (pedersen-precond ms))
  (equal (pedersen d ms) hs)
  :guard-hints (("Goal" :in-theory (enable pedersen-precond))))

; use instances (pedersen-spec d (list m0 m1 ... mN-1) (list h0 h1 ... h254))
; for N > 0 and d constant list of 8 bytes
