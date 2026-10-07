; (Floor of) base-2 logarithm (works on all positive rationals)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See rules in log2.lisp

(local (include-book "floor"))
(local (include-book "divide"))
(local (include-book "times"))

;; Returns the floor of the base 2 logarithm of the positive rational x.  Not meaningful for 0.
;; TODO: Rename log2 to floor-of-log2 ?
;; TODO: Generalize the base?
(defund log2 (x)
  (declare (xargs :guard (and (rationalp x)
                              (< 0 x))
                  :measure (if (and (rationalp x)
                                    (< 0 x))
                               (if (<= 2 x)
                                   (floor x 1)
                                 (if (< x 1)
                                     (floor (/ x) 1)
                                   0))
                             0)))
  (if (not (mbt (and (rationalp x)
                     (< 0 x))))
      0 ; todo: what value should we use here (negative infinity)?
    (if (<= 2 x)
        (+ 1 (log2 (/ x 2)))
      (if (< x 1)
          (+ -1 (log2 (* x 2)))
        ;; x is in [1,2), so its log2 is 0:
        0))))
