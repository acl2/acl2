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

;; See rules in ceiling-of-lg.lisp

;; The function CEILING-OF-LG computes the ceiling of the base-2 logarithm of
;; its argument, which must be a positive integer.
;; todo: generalize to rationals?  see log2.lisp
(defund ceiling-of-lg (x)
  (declare (xargs :guard (posp x))
           (type (integer 0 *) x))
  (integer-length (+ -1 x)))
