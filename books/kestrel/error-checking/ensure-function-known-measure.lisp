; Error Checking
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/system/get-measure" :dir :system)
(include-book "std/system/logic-function-namep" :dir :system)
(include-book "kestrel/error-checking/def-error-checker" :dir :system)

(local (xdoc::set-default-parents error-checking))

(def-error-checker ensure-function-known-measure
  ((fn (and (logic-function-namep fn (w state))
            (recursivep fn nil (w state)))
       "Function to check."))
  :short
  "Cause an error if a recursive function
   has an unknown measure (i.e. one with @(':?'))."
  :body
  (((not (eq (car (get-measure fn (w state))) :?))
    "~@0 must have a known measure, i.e. not one of the form (:? ...)."
    description))
  :verify-guards nil)
