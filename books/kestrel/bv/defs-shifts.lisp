; BV Library: Definitions of shift operations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;;logical shifts

(include-book "bvcat-def")
(include-book "slice-def")

;; Shift X left by SHIFT-AMOUNT places in a field of width WIDTH.  The least
;; significant bits of the result are 0.  Often we will let this open to bvcat
;; for reasoning.
(defund shl (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type (integer 0 *) width)
           (type integer x)
           (xargs :guard (<= shift-amount width)))
  (bvcat (- width shift-amount) x shift-amount 0))

;; Shift X right by SHIFT-AMOUNT places in a field of width WIDTH. The most
;; significant bits of the result are 0.
;; Perhaps this should be called zshr (zero-extending shift).
(defund shr (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type integer x)
           (type integer width) ;todo: require non-neg?
           (xargs :guard (<= shift-amount width)))
  (slice (+ -1 width) shift-amount x))
