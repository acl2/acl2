; A test of the boolean constraint R1CS gadget
;
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "boolean")
(include-book "std/testing/assert-equal" :dir :system)

;; Example boolean constraint circuit with the constrained variable 'b'.
(defconst *boolean-constraint*
  (make-boolean-constraint 'b))

(acl2::assert-equal
 *boolean-constraint*
 (r1cs-constraint
   '((1 b)) ; a
   '((1 b) (-1 1)) ; b
   '() ; c
   ))
