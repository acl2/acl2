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

(fty::defflexsum jvalue
  :short "Fixtype of Java values [JLS:4],
          excluding extended-exponent values [JLS:4.2.3]."
  :long
  (xdoc::topstring-p
   "To avoid a conflict with @(tsee value),
    we prefix @('value') with @('j') for the fixtype of Java values,
    and, for consistency,
    we do the same for recognizer, fixer, and equivalence.")
  (:primitive
   :fields ((get :type primitive-value :acc-body x))
   :ctor-body get
   :cond (primitive-value-p x))
  (:reference
   :fields ((get :type reference-value :acc-body x))
   :ctor-body get)
  :pred jvaluep
  :prepwork
  ((defrulel lemma
     (implies (reference-value-p x)
              (not (primitive-value-p x)))
     :enable (primitive-value-p
              boolean-value-p
              char-value-p
              byte-value-p
              short-value-p
              int-value-p
              long-value-p
              float-value-p
              double-value-p
              reference-value-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflexsum jvaluex
  :short "Fixtype of Java values [JLS:4],
          including extended-exponent values [JLS:4.2.3]."
  (:primitive
   :fields ((get :type primitivex-value :acc-body x))
   :ctor-body get
   :cond (primitivex-value-p x))
  (:reference
   :fields ((get :type reference-value :acc-body x))
   :ctor-body get)
  :pred jvaluexp
  :prepwork
  ((defrulel lemma
     (implies (reference-value-p x)
              (not (primitivex-value-p x)))
     :enable (primitivex-value-p
              primitive-value-p
              boolean-value-p
              char-value-p
              byte-value-p
              short-value-p
              int-value-p
              long-value-p
              float-value-p
              double-value-p
              floatx-value-p
              doublex-value-p
              reference-value-p))))
