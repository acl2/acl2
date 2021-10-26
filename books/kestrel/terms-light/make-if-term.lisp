; A utility for making an IF-term in a propositional context

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This requires the TEST to not be constant, because we can do better if it may be.
;; The result is equivalent to (if test then else) under iff.
(defun make-if-term (test then else)
  (declare (xargs :guard (and (pseudo-termp test)
                              (not (quotep test))
                              (pseudo-termp then)
                              (pseudo-termp else))))
  (if (equal then else)
      then
    (if (and (equal then *t*)
             (equal else *nil*))
        test ; avoids (if <test> t nil)
      `(if ,test ,then ,else))))
