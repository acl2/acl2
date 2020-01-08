; A utility to check whether a list is a permutation of another.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/lists-light/memberp-def" :dir :system)

;; TODO: move?
;; Like remove1 but does not require L to be a true-list.
(defun remove1$ (x l)
  (declare (xargs :guard t))
  (if (not (consp l))
      nil
    (if (equal x (first l))
        (rest l)
      (cons (first l)
            (remove1$ x (rest l))))))

;; TODO: move?
(defthm remove1$-becomes-remove1-equal
  (equal (remove1$ x l)
         (remove1-equal x l)))

;;;
;;; perm
;;;

;; Check whether the elements of x are a permutation of the elements of y.
;; Ignores the final cdrs of x and y.
(defund perm (x y)
  (declare (xargs :guard t))
  (if (not (consp x))
      (not (consp y))
    (and (memberp (first x) y) ;member-equal would require true-listp
         ;; Can't call remove1 since it requires a true-list:
         (perm (rest x) (remove1$ (first x) y)))))
