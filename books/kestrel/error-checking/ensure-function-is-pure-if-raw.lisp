; Error Checking Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "def-error-checker")

(include-book "kestrel/std/system/rawp" :dir :system)
(include-book "kestrel/std/system/pure-raw-p" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-is-pure-if-raw ((fn symbolp
                                                       "Value to check."))
  :verify-guards nil
  :parents (error-checking)
  :short "Cause an error if a function
          has raw Lisp code and is not whitelisted as pure."
  :body (((or (not (rawp fn state))
              (pure-raw-p fn))
          "~@0 has raw Lisp code, ~
           but it is not in the whitelist of ~
           known pure functions with raw Lisp code."
          description)))
