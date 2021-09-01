; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification of the gadget in [ZPS:A.3.3.6].

(in-package "ZCASH")

(include-book "a-3-3-1-spec")

(define nonsmall-order-spec (u v)
  :guard (and (fep u (jubjub-q))
              (fep v (jubjub-q)))
  (and (affine-edwards-spec u v)
       (b* ((point (ecurve::point-finite u v))
            (8*point (ecurve::twisted-edwards-mul 8 point (jubjub-curve))))
         (and (equal (ecurve::point-kind 8*point) :finite)
              (not (equal (ecurve::point-finite->x 8*point) 0)))))
  :guard-hints (("Goal" :in-theory (enable affine-edwards-spec
                                           point-on-jubjub-p))))
