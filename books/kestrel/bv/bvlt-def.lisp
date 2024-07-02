; Unsigned bit-vector "less than" comparison, etc. (definitions only)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvchop")

;unsigned less-than
(defund bvlt (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (< (bvchop size x)
     (bvchop size y)))

;unsigned less-than-or-equal
(defun bvle (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (not (bvlt size y x)))

;unsigned greater-than
(defun bvgt (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (bvlt size y x))

;unsigned greater-than-or-equal
(defun bvge (size x y)
  (declare (type integer x y)
           (type (integer 0 *) size))
  (not (bvlt size x y)))
