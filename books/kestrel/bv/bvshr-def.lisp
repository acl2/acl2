; BV Library: Definitions of logical right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "slice-def")

;; Shift X right by SHIFT-AMOUNT places in a field of width WIDTH. The most
;; significant bits of the result thus are usually 0.
;; Perhaps this should be called zshr (zero-extending shift).
;; TODO: Should this chop the shift-amount argument?
(defund bvshr (width x shift-amount)
  (declare (xargs :guard (and (natp shift-amount)
                              (integerp x)
                              (integerp width)
                              (<= shift-amount width) ;todo: relax (return 0)?
                              )
                  :split-types t)
           (type (integer 0 *) shift-amount width)
           (type integer x))
  (let ((width (mbe :logic (nfix width) :exec width))
        (shift-amount (mbe :logic (nfix shift-amount) :exec shift-amount)))
    (slice (+ -1 width) shift-amount x)))
