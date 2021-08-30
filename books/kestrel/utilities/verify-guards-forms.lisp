; Utilities for recognizing and manipulating verify-guards forms
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defconst *verify-guards-types* '(verify-guards verify-guards+))

;; Recognize a verify-guards form.
(defund verify-guards-formp (form)
  (declare (xargs :guard t))
  (and (true-listp form)
       (<= 1 (len (fargs form))) ; must have at least the name
       (member-eq (first form) *verify-guards-types*)
       (symbolp (second form))  ; the function name
       (keyword-value-listp (rest (fargs form))) ;skip the name argument
       ))
