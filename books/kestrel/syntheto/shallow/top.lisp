; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "types")

(include-book "expressions")
(include-book "expressions-macros")

(include-book "functions")

(include-book "composite-types")

(include-book "specifications")

(include-book "theorems")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shallow-embedding
  :parents (syntheto)
  :short "Macros that represent Syntheto directly in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a shallow embedding of Syntheto in ACL2,
     intended for quick generation of ACL2 definitions from an IDE.
     This is work in progress."))
  :order-subtopics t)
