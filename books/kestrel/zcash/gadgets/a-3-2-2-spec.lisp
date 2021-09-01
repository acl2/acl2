; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification of the gadget in [ZPS:A.3.2.2].

(in-package "ZCASH")

(include-book "kestrel/prime-fields/fe-listp" :dir :system)
(include-book "kestrel/zcash/jubjub" :dir :system)

(define range-check-spec (as cs)
  :guard (and (pfield::fe-listp as (jubjub-q))
              (bit-listp cs)
              (consp as)
              (equal (len cs) (len as))
              (not (equal (car (last cs)) 0)))
  (b* ((a (range-check-spec-aux as 1))
       (c (acl2::lebits=>nat cs)))
    (<= a c))

  :prepwork
  ((define range-check-spec-aux (as pow2)
     :guard (and (pfield::fe-listp as (jubjub-q))
                 (posp pow2))
     :returns (result rationalp :hyp :guard)
     :verify-guards :after-returns
     (cond ((endp as) 0)
           (t (+ (* (car as) pow2)
                 (range-check-spec-aux (cdr as) (* 2 pow2))))))))

; use instances (range-check-spec (a0 a1 ... aN-1) (c0 c1 ... cN-1))
; for N > 0 and ci constants
