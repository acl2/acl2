; A function to fix a value to a positive integer
;
; Copyright (C) 2019-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Also in std?
(defun pos-fix (x)
  (declare (xargs :guard t))
  (if (posp x)
      x
    1))

(defthm pos-fix-when-posp
  (implies (posp x)
           (equal (pos-fix x)
                  x)))
