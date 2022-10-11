; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "concrete-syntax-rules")

(include-book "operations/well-formedness")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection concrete-syntax-rules-validation
  :parents (concrete-syntax-rules)
  :short "Validation of the concrete syntax rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the concrete syntax rules are well-formed.")
   (xdoc::p
    "Additonal properties, such as closure,
     do not hold just for the concrete syntax rules:
     they must be completed with (some of) the core rules.
     See @(see concrete-syntax-validation).")
   (xdoc::p
    "As done for @(see core-rules-validation),
     we put the validation of the concrete syntax rules in a separate file
     so that their definition does not depend on grammar @(see operations)."))

  (defruled rulelist-wfp-of-*concrete-syntax-rules*
    (rulelist-wfp *concrete-syntax-rules*)))
