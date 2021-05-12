; Tests of the R1CS formalization
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "r1cs")

;; Surprisingly, defaggregate does not check the keys of the alist!  We should
;; change it so that this is not a theorem:
(thm (r1cs-constraintp-aux '((foobar . nil))))

;; Ensure ill-formed things are not considered constraints:
(thm (not (r1cs-constraintp '((foobar . nil)))))
