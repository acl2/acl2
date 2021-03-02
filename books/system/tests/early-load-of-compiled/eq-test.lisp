; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This test checks that *eqt1* and *eqt2* below are EQ, something that was true
; before the changes in mid-February 2021 as well as after -- but we want to
; preserve that property through the future!  We have timed include-book at
; 0.34 seconds after the mid-February 2021 changes, but at 0.97 seconds before.

(in-package "ACL2")

(defun eqt-big-tree (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) nil)
        (t (cons (make-list n :initial-element n)
                 (eqt-big-tree (1- n))))))

(defconst *eqt1* (eqt-big-tree 1000))
(defconst *eqt2* *eqt1*)

(defconst *eqt-big-size* 10000000)

(defconst *eqt-list1*
  (make-list *eqt-big-size* :initial-element *eqt1*))

(defconst *eqt-list2*
  (make-list *eqt-big-size* :initial-element *eqt2*))

(assert-event (equal *eqt-list1* *eqt-list2*)
              :on-skip-proofs t)
