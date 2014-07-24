; ACL2 books using the bdd hints
; Copyright (C) 1997  Computational Logic, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Written by:  Matt Kaufmann
; email:       Matt_Kaufmann@aus.edsr.eds.com
; Computational Logic, Inc.
; 1717 West Sixth Street, Suite 290
; Austin, TX 78703-4776 U.S.A.

(in-package "ACL2")

(defun b-and (x y)
  (declare (xargs :mode :logic
                  :verify-guards t))
  (if x
      (if y t nil)
    nil))

(defun b-or (x y)
  (declare (xargs :mode :logic
                  :verify-guards t))
  (if x
      t
    (if y t nil)))

(defun b-xor (a b)
  (declare (xargs :mode :logic
                  :verify-guards t))
  (if a
      (if b nil t)
    (if b t nil)))

(defthm b-and-comm
  (equal (b-and x y)
         (b-and y x)))

(defthm b-or-comm
  (equal (b-or x y)
         (b-or y x)))

(defthm b-xor-comm
  (equal (b-xor x y)
         (b-xor y x)))

; The rest are theorems that one might prove, but we don't.

#|
(defthm b-xor-x-x
  (equal (b-xor x x) nil))

(defthm b-and-x-x
  (equal (b-and x x)
         (if x t nil)))

(defthm b-or-x-x
  (equal (b-or x x)
         (if x t nil)))

(defthm b-xor-t-x
  (equal (b-xor t x)
         (if x nil t)))

(defthm b-xor-nil-x
  (equal (b-xor nil x)
         (if x t nil)))

(defthm b-and-t-x
  (equal (b-and t x)
         (if x t nil)))

(defthm b-and-nil-x
  (equal (b-and nil x) nil))

(defthm b-or-t-x
  (equal (b-or t x) t))

(defthm b-or-nil-x
  (equal (b-or nil x)
         (if x t nil)))
|#
