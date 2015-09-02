; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

;; (include-book "log")

(set-enforce-redundancy nil)

(include-book "../lib1/top")

(set-inhibit-warnings "theory") ; avoid warning in the next event

;;; add on extra definition to bits

(defun bitvec (x n)
  (if (bvecp x n) x 0))

