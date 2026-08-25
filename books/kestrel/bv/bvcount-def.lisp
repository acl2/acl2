; Counting the number of 1 bits: definition
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See rules in bvcount.lisp.

(include-book "getbit-def")

;; Count the number of 1 bits in X, which should be SIZE bits wide.  The result
;; fits in B bits where B is (integer-length SIZE).
(defund bvcount (size x)
  (declare (xargs :guard (and (natp size)
                              (integerp x))))
  (if (zp size)
      0
    (+ (getbit (+ -1 size) x)
       (bvcount (+ -1 size) x))))
