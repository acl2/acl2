; ACL2-2026 Workshop Paper on DEFINDUCTIVE
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/definductive" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains details of the JUST-0 example in Section 4.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A non-recursive definition.

(definductive just-0
  :preds ((p x))
  :irules ((zero () (p 0))))

; Since any valid proof tree of P forces X to be 0...

(defrule zero-when-p-proof-validp
  (implies (p-proof-validp proof x)
           (equal x 0))
  :rule-classes nil
  :enable (p-proof-validp
           p-zero-validp))

; ... X must be 0 to satisfy P.

(defrule zero-when-p
  (implies (p x)
           (equal x 0))
  :rule-classes nil
  :enable p
  :use (:instance zero-when-p-proof-validp (proof (p-proof x))))

; P is satisfied by 0.

(defruled p-when-zero
  (implies (equal x 0)
           (p x))
  :enable p-zero)

; Thus, P is satisfied exactly by 0.

(defruled p-is-zero
  (equal (p x)
         (equal x 0))
  :use (zero-when-p p-when-zero))
