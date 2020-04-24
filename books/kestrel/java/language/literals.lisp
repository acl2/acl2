; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "integer-literals")
(include-book "floating-point-literals")
(include-book "character-literals")
(include-book "string-literals")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ literals
  :parents (syntax)
  :short "Java literals [JLS:3.10]."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum literal
  :short "Fixtype of literals."
  :long
  (xdoc::topstring
   (xdoc::p
    "This corresponds to the grammar rule for @('literal') [JLS:3.10].")
   (xdoc::p
    "Note that we just use the built-in ACL2 booleans
     for the boolean literals, since they are so simple."))
  (:integer ((get integer-literal)))
  (:fpoint ((get floating-point-literal)))
  (:char ((get char-literal)))
  (:string ((get string-literal)))
  (:boolean ((get bool)))
  (:null ())
  :pred literalp)
