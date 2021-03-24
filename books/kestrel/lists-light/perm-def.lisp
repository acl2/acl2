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

(include-book "memberp-def")
(include-book "remove1-dollar-def")

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
