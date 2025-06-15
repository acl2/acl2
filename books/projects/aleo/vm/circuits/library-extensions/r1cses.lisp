; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "kestrel/crypto/r1cs/sparse/r1cs" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule r1cs::valuation-binds-allp-of-last
  (implies (r1cs::valuation-binds-allp valuation vars)
           (r1cs::valuation-binds-allp valuation (last vars))))

(defrule r1cs::valuation-bindsp-of-car-when-valuation-binds-allp
  (implies (and (r1cs::valuation-binds-allp valuation vars)
                (consp vars))
           (r1cs::valuation-bindsp valuation (car vars))))

(defrule r1cs::valuation-binds-allp-of-take
  (implies (and (r1cs::valuation-binds-allp valuation vars)
                (<= n (len vars)))
           (r1cs::valuation-binds-allp valuation (take n vars)))
  :enable r1cs::valuation-binds-allp)

(defrule r1cs::valuation-binds-allp-of-cdr
  (implies (r1cs::valuation-binds-allp valuation vars)
           (r1cs::valuation-binds-allp valuation (cdr vars)))
  :enable r1cs::valuation-binds-allp)

(defrule r1cs::valuation-binds-allp-of-nil
  (r1cs::valuation-binds-allp valuation nil)
  :enable r1cs::valuation-binds-allp)
