; Zcash Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
