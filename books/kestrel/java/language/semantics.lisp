; Java Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

; the order of the following INCLUDE-BOOKs determines
; the order of the subtopics of the SEMANTICS topic below:
(include-book "floating-point-value-set-parameters")
(include-book "floating-point-placeholders")
(include-book "primitive-values")
(include-book "primitive-function-macros")
(include-book "primitive-operations")
(include-book "primitive-conversions")
(include-book "pointers")
(include-book "reference-values")
(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ semantics
  :parents (language)
  :short "A formal model of some aspects of the semantics of Java."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is expected that more aspects of the semantics of Java
     will be formalized here over time."))
  :order-subtopics t)
