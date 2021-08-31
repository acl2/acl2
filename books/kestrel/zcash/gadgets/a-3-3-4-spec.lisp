; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification of the gadget in [ZPS:A.3.3.4].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub-montgomery" :dir :system)

(define montgomery-add-precond (x1 y1 x2 y2)
  :guard (and (fep x1 (jubjub-q))
              (fep y1 (jubjub-q))
              (fep x2 (jubjub-q))
              (fep y2 (jubjub-q)))
  (and (ecurve::point-on-montgomery-p (ecurve::point-finite x1 y1)
                                      (jubjub-montgomery-curve))
       (ecurve::point-on-montgomery-p (ecurve::point-finite x2 y2)
                                      (jubjub-montgomery-curve))
       (not (equal x1 x2))))

(define montgomery-add-spec (x1 y1 x2 y2 x3 y3)
  :guard (and (fep x1 (jubjub-q))
              (fep y1 (jubjub-q))
              (fep x2 (jubjub-q))
              (fep y2 (jubjub-q))
              (fep x3 (jubjub-q))
              (fep y3 (jubjub-q))
              (montgomery-add-precond x1 y1 x2 y2))
  (equal (ecurve::montgomery-add (ecurve::point-finite x1 y1)
                                 (ecurve::point-finite x2 y2)
                                 (jubjub-montgomery-curve))
         (ecurve::point-finite x3 y3))
  :guard-hints (("Goal" :in-theory (enable montgomery-add-precond))))
