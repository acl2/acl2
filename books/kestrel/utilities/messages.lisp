; Messages
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc message-utilities
  :parents (kestrel-utilities)
  :short "Utilities for <see topic='@(url msgp)'>messages</see>.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-msgp (x)
  :returns (yes/no booleanp)
  :parents (message-utilities)
  :short "Recognize @('nil') and messages."
  (or (msgp x)
      (null x))
  ///

  (defrule maybe-msgp-when-msgp
    (implies (msgp x)
             (maybe-msgp x)))

  (defrule maybe-msgp-of-nil
    (maybe-msgp nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist msg-listp (x)
  (msgp x)
  :parents (message-utilities)
  :short "Recognize true lists of messages."
  :true-listp t
  :elementp-of-nil nil)
