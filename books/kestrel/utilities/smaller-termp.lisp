; A syntactic test to compare term sizes.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2017-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Check whether x is a strictly smaller term than y.  Note that term-order is
;; reflexive, so it is like a <= test.  So smaller-termp is like the
;; corresponding < test.
(defun smaller-termp (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (not (term-order y x)))

(defthm booleanp-of-smaller-termp
  (booleanp (smaller-termp x y)))
