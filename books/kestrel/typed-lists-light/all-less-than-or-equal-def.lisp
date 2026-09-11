; Just the definition of all-<=
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See all-less-than-or-equal.lisp for theorems.

(defun all-<= (x n)
  (declare (xargs :guard (and (rational-listp x) (rationalp n))))
  (if (atom x)
      t
    (and (<= (first x) n)
         (all-<= (rest x) n))))
