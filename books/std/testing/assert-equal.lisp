; Standard Testing Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "assert-bang")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection assert-equal
  :parents (std/testing errors)
  :short "Abbreviation for calling @(tsee assert!) on an equality."
  :long "@(def assert-equal)"
  (defmacro assert-equal (x y)
    `(assert! (equal ,x ,y))))
