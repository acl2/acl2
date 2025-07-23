; Base-2 logarithm (rounded up)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The function CEILING-OF-LG computes the ceiling of the base-2 logarithm of
;; its argument.

;; See rules in ceiling-of-lg.lisp

(defund ceiling-of-lg (x)
  (declare (type integer x))
  (integer-length (+ -1 x)))
