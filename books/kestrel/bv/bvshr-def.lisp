; BV Library: Definitions of logical right shift
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
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
(defund bvshr (width x shift-amount)
  (declare (type (integer 0 *) shift-amount)
           (type integer x)
           (type integer width) ;todo: require non-neg?
           (xargs :guard (<= shift-amount width)))
  (slice (+ -1 width) shift-amount x))
