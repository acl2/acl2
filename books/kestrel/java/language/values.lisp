; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "primitive-values")
(include-book "reference-values")

; Added 7/1/2021 by Matt K. after 3 successive ACL2(p) certification failures:
(set-waterfall-parallelism nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ values
  :parents (semantics)
  :short "Java values [JLS:4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A value is either a primitive value or a reference value [JLS:4.1].")
   (xdoc::p
    "Since in our model we have primitive values
     with and without extended-exponent values [JLS:4.2.3],
     here we correspondingly formalize values
     with and without extended-exponent values.")
   (xdoc::p
    "To avoid conflict or confusion with @(tsee value),
     we prefix @('value') with @('j') in ACL2 fixtype and function names
     that pertain to Java values."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum jvalue
  :short "Fixtype of Java values [JLS:4],
          excluding extended-exponent values [JLS:4.2.3]."
  :long
  (xdoc::topstring-p
   "To avoid a conflict with @(tsee value),
    we prefix @('value') with @('j') for the fixtype of Java values,
    and, for consistency,
    we do the same for recognizer, fixer, and equivalence.")
  (:primitive primitive-value)
  (:reference reference-value)
  :pred jvaluep
  :prepwork
  ((defrulel lemma
     (implies (reference-valuep x)
              (not (primitive-valuep x)))
     :enable (primitive-valuep
              boolean-valuep
              char-valuep
              byte-valuep
              short-valuep
              int-valuep
              long-valuep
              float-valuep
              double-valuep
              reference-valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum jvaluex
  :short "Fixtype of Java values [JLS:4],
          including extended-exponent values [JLS:4.2.3]."
  (:primitive primitivex-value)
  (:reference reference-value)
  :pred jvaluexp
  :prepwork
  ((defrulel lemma
     (implies (reference-valuep x)
              (not (primitivex-valuep x)))
     :enable (primitivex-valuep
              primitive-valuep
              boolean-valuep
              char-valuep
              byte-valuep
              short-valuep
              int-valuep
              long-valuep
              float-valuep
              double-valuep
              floatx-valuep
              doublex-valuep
              reference-valuep))))
