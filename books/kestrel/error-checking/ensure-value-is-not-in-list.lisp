; Error Checking Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "def-error-checker")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-error-checker ensure-value-is-not-in-list
  ((x "Value to check.")
   (list true-listp "List that must not include @('x') as member.")
   (list-description msgp "Description of @('list') for the error message."))
  :parents (error-checking)
  :short "Cause an error if a value is a member of a list."
  :body (((not (member-equal x list))
          "~@0 must not be ~@1, but it is."
          description list-description)))
