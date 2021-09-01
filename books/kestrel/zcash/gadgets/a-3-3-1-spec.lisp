; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Specification of the gadget in [ZPS:A.3.3.1].

(in-package "ZCASH")

(include-book "kestrel/zcash/jubjub" :dir :system)

(define affine-edwards-spec (u v)
  :guard (and (fep u (jubjub-q)) (fep v (jubjub-q)))
  (point-on-jubjub-p (ecurve::point-finite u v)))
