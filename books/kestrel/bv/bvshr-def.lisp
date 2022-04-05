; BV Library: Definitions of logical right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "slice-def")

;; Shift X right by SHIFT-AMOUNT places in a field of width WIDTH. The most
;; significant bits of the result are 0.
;; Perhaps this should be called zshr (zero-extending shift).
;width must be positive (allow zero?). it's the width of x (to start out)
;fills with 0's at the top
;so if shift-amount is positive this will be a shorter bit-vector
;in no case will the result be longer than width bits
;hmmm. do we plan to enable or disable this?
(defund bvshr (width x shift-amount)
  (declare (xargs :guard (and (natp shift-amount)
                              (integerp x)
                              (integerp width)
                              (<= shift-amount width) ;what happens if they're equal? i guess we get 0
                              )
                  :split-types t)
           (type (integer 0 *) shift-amount width)
           (type integer x))
  (slice (+ -1 width) shift-amount x))
