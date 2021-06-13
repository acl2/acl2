; A lightweight book about the built-in function abs
;
; Copyright (C) 2016-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Consider disabling abs

(defthm abs-when-non-neg
  (implies (and (<= 0 x)
                (rationalp x))
           (equal (abs x)
                  x)))
