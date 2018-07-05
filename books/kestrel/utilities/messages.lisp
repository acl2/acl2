; Structured Messages
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-msgp (x)
  :returns (yes/no booleanp)
  :parents (kestrel-utilities)
  :short "Recognize @('nil') and structured messages."
  :long
  "<p>
   Structured messages are
   constructed by @(tsee msg) and recognized by @(tsee msgp).
   </p>"
  (or (msgp x)
      (null x))
  ///

  (defrule maybe-msgp-when-msgp
    (implies (msgp x)
             (maybe-msgp x)))

  (defrule maybe-msgp-of-nil
    (maybe-msgp nil)))
