; A variant of remove1-equal
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Like remove1 but does not require L to be a true-list.
(defun remove1$ (x l)
  (declare (xargs :guard t))
  (if (not (consp l))
      nil
    (if (equal x (first l))
        (rest l)
      (cons (first l)
            (remove1$ x (rest l))))))

(defthm remove1$-becomes-remove1-equal
  (equal (remove1$ x l)
         (remove1-equal x l)))
