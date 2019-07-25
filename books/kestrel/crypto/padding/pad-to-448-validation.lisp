; Crypto Library: Validation of pad-to-448
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PADDING")

(include-book "pad-to-448")
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))

;; Note that pad-to-448-number-of-zeros-type shows that the number of zeros is
;; non-negative.

;; Any non-negative solution to the equation "l+1+k is congruent to 448 (mod
;; 512)" is at least as big as the k we choose, so our k is the smallest
;; non-negative solution.
(defthm pad-to-448-number-of-zeros-correct
  (implies (and (natp other-solution)
                (equal (mod (+ l 1 other-solution) 512)
                       448)
                (natp l))
           (<= (pad-to-448-number-of-zeros l)
               other-solution))
  :hints (("Goal" :in-theory (enable pad-to-448-number-of-zeros))))
