; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "concrete-syntax")

(include-book "../operations/well-formedness")
(include-book "../operations/closure")
(include-book "../operations/in-terminal-set")
(include-book "../operations/plugging")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection concrete-syntax-validation
  :parents (concrete-syntax)
  :short "Validation of the concrete syntax grammar."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that rules of the grammar of the ABNF concrete syntax:")
   (xdoc::ul
    (xdoc::li
     "Are well-formed.")
    (xdoc::li
     "Are closed.")
    (xdoc::li
     "Generate only strings of ASCII codes.")
    (xdoc::li
     "Are the same (module ordering) as the resulting of
      plugging the core rules into the concrete syntax rules."))
   (xdoc::p
    "These theorems are in a separate file
     so that the definition of the concrete syntax
     does not depend on the grammar @(see operations),
     as also done for @(see core-rules-validation)
     and for @(see concrete-syntax-rules-validation)."))

  (defruled rulelist-wfp-of-*grammar*
    (rulelist-wfp *grammar*))

  (defruled rulelist-closedp-of-*grammar*
    (rulelist-closedp *grammar*))

  (defruled ascii-only-*grammar*
    (rulelist-in-termset-p *grammar*
                           (integers-from-to 0 127)))

  (defruled plugging-yields-*grammar*
    (set-equiv (plug-rules *concrete-syntax-rules* *core-rules*)
               *grammar*)))
