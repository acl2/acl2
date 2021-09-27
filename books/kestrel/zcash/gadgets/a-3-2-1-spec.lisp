; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification of the gadget in [ZPS:A.3.2.1].

(in-package "ZCASH")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/zcash/jubjub" :dir :system)

(define [un]packing-precond (bs)
  :guard (pfield::fe-listp bs (jubjub-q))
  (bit-listp bs))

(define [un]packing-spec (a bs)
  :guard (and (fep a (jubjub-q))
              (fe-listp bs (jubjub-q))
              (consp bs)
              ([un]packing-precond bs))
  (equal a (mod (acl2::lebits=>nat bs) (jubjub-q)))
  :guard-hints (("Goal" :in-theory (enable [un]packing-precond))))

; use instances ([un]packing-spec a (list b0 b1 b2 ... bN-1))
; for N > 0
