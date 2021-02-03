; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "primitive-types")
(include-book "reference-types")

(include-book "kestrel/fty/defflatsum" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ types
  :parents (syntax)
  :short "Java types [JLS:4]."
  :long
  (xdoc::topstring
   (xdoc::p
    "A type is either a primitive type or a reference type [JLS:4.1].
     Here we formalize this notion."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defflatsum jtype
  :short "Fixtype of Java types [JLS:4.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "To avoid a conflict with the use of the symbol @('type') in "
    (xdoc::seetopic "acl2::declare" "type declarations")
    ", we prefix @('type') with @('j') for the fixtype of Java types,
     and, for consistency,
     we do the same for recognizer, fixer, and equivalence."))
  (:primitive primitive-type)
  (:reference reference-type)
  :pred jtypep
  :prepwork
  ((defrulel lemma
     (implies (reference-typep x)
              (not (primitive-typep x)))
     :enable (primitive-typep
              reference-typep))))
