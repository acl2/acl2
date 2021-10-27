; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "abstract-syntax")
;; EM: Temporary
(include-book "absynt-literal-adapter")

;; Serialize ASTs.
(include-book "make-myself")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ language
  :parents (syntheto)
  :short "A formalization of the Syntheto language in ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a deep embedding of Syntheto in ACL2.
     We explicitly formalize the syntax of the languge,
     along with its semantics.
     This is work in progress."))
  :order-subtopics t)
