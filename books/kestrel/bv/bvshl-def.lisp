; BV Library: Definition of left shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bvcat-def")

;; Shift X left by SHIFT-AMOUNT places in a field of width WIDTH.  The least
;; significant bits of the result are 0.  Often we will let this open to bvcat
;; for reasoning.
;; Often we will let this open to bvcat.
;; We expect (<= shift-amount width).
;see bvshl-rewrite-with-bvchop for a version that puts a bvchop around x to help us simplify stuff -- old comment?
;; TODO: Consider chopping the shift amount (but what if the width is not a power of 2)?
(defund bvshl (width x shift-amount)
  (declare (xargs :guard (and (natp shift-amount)
                              (natp width)
                              (<= shift-amount width)
                              (integerp x))
                  :split-types t)
           (type (integer 0 *) shift-amount width)
           (type integer x))
  (let ((width (mbe :logic (nfix width) :exec width))
        (shift-amount (mbe :logic (nfix shift-amount) :exec shift-amount)))
    (bvcat (- width shift-amount) x shift-amount 0)))
