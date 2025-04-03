; Signed bit-vector "less than" comparison
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "logext-def")

;;signed less-than
(defund sbvlt (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (< (logext n x)
     (logext n y)))

;;signed less-than-or-equal
(defun sbvle (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (not (sbvlt n y x)))

;;signed greater-than
(defun sbvgt (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (sbvlt n y x))

;;signed greater-than-or-equal
(defun sbvge (n x y)
  (declare (type (integer 1 *) n)
           (type integer x)
           (type integer y))
  (not (sbvlt n x y)))
