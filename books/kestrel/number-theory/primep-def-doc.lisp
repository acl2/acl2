; Number Theory Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RTL")

(include-book "primep-def")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc primep
  :short "Recognizer of prime numbers."
  :parents (acl2::number-theory)
  :long
  (xdoc::topstring
   (xdoc::p
    "This is taken from the RTL library.")
   (xdoc::@def "primep")
   (xdoc::@def "least-divisor")
   (xdoc::@def "divides")))
