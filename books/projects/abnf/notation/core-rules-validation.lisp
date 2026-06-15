; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "core-rules")
(include-book "../grammar-operations/well-formedness")
(include-book "../grammar-operations/closure")
(include-book "../grammar-operations/in-terminal-set")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection core-rules-validation
  :parents (notation)
  :short "Validation of the core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that the core rules:")
   (xdoc::ul
    (xdoc::li
     "Are well-formed.")
    (xdoc::li
     "Are closed.")
    (xdoc::li
     "Generate only strings of octets.")
    (xdoc::li
     "Without the @('OCTET') rule,
      generate only strings of ASCII codes."))
   (xdoc::p
    "These validation theorems depend on some "
    (xdoc::seetopic "grammar-operations" "grammar operations")
    ". Thus, we put them in a separate file,
     avoiding a dependency of the file that defines the core rules
     on the grammar operations."))

  (defruled rulelist-wfp-of-*core-rules*
    (rulelist-wfp *core-rules*))

  (defruled rulelist-closedp-of-*core-rules*
    (rulelist-closedp *core-rules*))

  (defruled octet-only-*core-rules*
    (rulelist-in-termset-p *core-rules* (integers-from-to 0 255)))

  (defruled ascii-only-*core-rules*-without-*octet*
    (rulelist-in-termset-p (remove-equal *rule_octet* *core-rules*)
                           (integers-from-to 0 127))))
