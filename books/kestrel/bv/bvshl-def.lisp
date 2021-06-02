; BV Library: Definitions left shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
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
(defund bvshl (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type (integer 0 *) width)
           (type integer x)
           (xargs :guard (<= shift-amount width)))
  (bvcat (- width shift-amount) x shift-amount 0))
