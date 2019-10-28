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
; the order of the subtopics of the LANGUAGE topic below:
(include-book "syntax")
(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ language
  :parents (java)
  :short "A formal model of some aspects of the Java language."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is expected that more aspects of the Java language
     will be formalized here over time."))
  :order-subtopics t)
