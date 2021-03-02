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

(include-book "kestrel/std/system/definedp" :dir :system)
(include-book "kestrel/std/system/logic-function-namep" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-function-is-defined
  ((fn (logic-function-namep fn (w state)) "Function to check."))
  :short "Cause an error if a logic-mode function is not defined."
  :body (((definedp fn (w state))
          "~@0 must be defined." description)))
