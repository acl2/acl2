; A lightweight book introducing list-equiv.
;
; For most of this material, see the copyright in std/.
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book just cherry-picks the definition of list-equiv from std.

;; Same as in std/.
;; TODO: deprecate?
(defmacro list-fix (x) `(true-list-fix ,x))

;; Same as in std/.
;; Checks that two lists are the same except perhaps for their final cdrs.
(defund fast-list-equiv (x y)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp y)
           (equal (car x) (car y))
           (fast-list-equiv (cdr x) (cdr y)))
    (atom y)))

;; Same as in std/.
;; Checks that two lists are the same except perhaps for their final cdrs.
(defund list-equiv (x y)
  (mbe :logic (equal (list-fix x) (list-fix y))
       :exec (fast-list-equiv x y)))

(verify-guards list-equiv
  :hints (("Goal" :in-theory (enable fast-list-equiv))))
