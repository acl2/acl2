; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "system/top" :dir :system)

(include-book "acceptable-rewrite-rule-p")
(include-book "invariant-risk")
(include-book "irrelevant-formals")
(include-book "non-parallel-book")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc std/system
  :parents (std)
  :short
  (xdoc::topstring
   "A library that complements the "
   (xdoc::seetopic "system-utilities" "built-in system utilities")
   " with theorems and with non-built-in system utilities.")
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a start towards a comprehensive library.
     Some candidate utilities are under @('[books]/kestrel/std').")))
