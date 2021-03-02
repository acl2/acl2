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

(include-book "kestrel/std/system/function-namep" :dir :system)
(include-book "kestrel/std/system/guard-verified-p" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-is-guard-verified
  ((fn (function-namep fn (w state)) "Function to check."))
  :short "Cause an error if a function is not guard-verified."
  :body (((guard-verified-p fn (w state))
          "~@0 must be guard-verified." description)))
