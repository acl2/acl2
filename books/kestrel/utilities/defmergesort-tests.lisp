; Tests for defmergesort
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defmergesort")
(include-book "deftest")

(deftest
  (defmergesort merge-sort-< merge-< < real/rationalp))

;; Same but with no extra theorems:
(deftest
  (defmergesort merge-sort-< merge-< < real/rationalp :extra-theorems nil)
  (defun perm (x) x) ; fake, just checks that perm didn't get brought in
  )

(deftest
  (in-theory nil) ;make sure the proofs still work with no rules enabled
  ;; TODO: We should probably produce an applicability condition that the guard of <
  ;; is satisfied by items that satisfy real/rationalp.
  (defmergesort merge-sort-< merge-< < real/rationalp))

;; A test with :verify-guards nil
(deftest
  (defun my< (x y) (< x y))
  (defmergesort merge-sort-my< merge-my< my< rationalp :verify-guards nil))

;; A test where there are elements that are equivalent but not equal (lists of the same length)
(deftest
  (defun len< (x y) (declare (xargs :guard (and (true-listp x) (true-listp y)))) (< (len x) (len y)))
  (defmergesort merge-sort-len< merge-len< len< true-listp :verify-guards nil))
