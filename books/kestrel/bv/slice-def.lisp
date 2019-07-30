; BV Library: The definition of slice
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See slice.lisp for theorems about slice.

(include-book "bvchop-def")
(include-book "logtail-def")

;; Extract the slice of the bit vector VAL from bit HIGH down to bit LOW.
;; Similar to bits in books/rtl.
(defund slice (high low val)
  (declare (type integer val high)
           (type (integer 0 *) low)
           (xargs :guard (<= (+ -1 low) high))) ;a bit odd
  (let ((low (mbe :exec low :logic (ifix low)))
        (high (mbe :exec high :logic (ifix high))))
    (bvchop (+ 1 high (- low)) (logtail low val))))
