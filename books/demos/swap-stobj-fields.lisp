; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book demonstrates how to swap two stobj fields of a given stobj.
; It also emphasizes that the parent stobj is updated implicitly after updating
; child fields.

(in-package "ACL2")

; A ``child'' type stobj:
(defstobj row
  (coefs :type (array double-float (4)) :initially #d0.0D0)
  (gaps :type (array integer (4)) :initially 0))

; A ``parent'' stobj:
(defstobj A
  (upper :type (array row (4)))
  (lower :type (array row (4))))

; The challenge is to swap (upperi 1 A) with (loweri 2 A).  Notice that the
; objects to swap are themselves row-type stobjs.

; We introduce the following stobj, congruent to row, in order to hold two
; different rows from A.

(defstobj rowprime 
  (coefsprime :type (array double-float (4)) :initially #d0.0D0)
  (gapsprime :type (array integer (4)) :initially 0)
  :congruent-to row)

; First, here are three failed attempts to code the swap function,
; swap-upper-1-lower-2 with an error message telling me I should use stobj-let.
; The first failed attempt shows the necessity of using stobj-let (even though
; there are no reads or writes for the child stobj).

#|
(defun swap-upper-1-lower-2 (a)
  (declare (xargs :stobjs (a)
                   :verify-guards nil))
  (let* ((row (upperi 1 a))
         (rowprime (loweri 2 a))
         (a (update-upperi 1 rowprime a))
         (a (update-loweri 2 row a)))
    a))


ACL2 Error [Translate] in ( DEFUN SWAP-UPPER-1-LOWER-2 ...):  It is
illegal to call UPPERI because it is a stobj updater or accessor for
a field of stobj type.  For a way to generate such a call, see :DOC
stobj-let.  Note:  this error occurred in the context (UPPERI 1 A).
|#

; The second snd third attempts do use stobj-let, but they attempt to update
; child stobj field directly rather than using stobj-let.

#|
(defun swap-upper-1-lower-2 (a)
  (declare (xargs :stobjs (a)
                  :verify-guards nil))
  (stobj-let ((row (upperi 1 a))
              (rowprime (loweri 2 a)))
             (row rowprime)
             (mv row rowprime)
             (let* ((a (update-upperi 1 rowprime a))
                    (a (update-loweri 2 row a)))
               a)))


ACL2 Error [Translate] in ( DEFUN SWAP-UPPER-1-LOWER-2 ...):  It is
illegal to call UPDATE-UPPERI because it is a stobj updater or accessor
for a field of stobj type.  For a way to generate such a call, see
:DOC stobj-let.  Note:  this error occurred in the context 
(UPDATE-UPPERI 1 ROWPRIME A).
|#

#|
(defun swap-upper-1-lower-2 (a)
  (declare (xargs :stobjs (a)
                  :verify-guards nil))
  (stobj-let ((row (upperi 1 a))
              (rowprime (loweri 2 a)))
             (a)
             (let* ((a (update-upperi 1 rowprime a))
                    (a (update-loweri 2 row a)))
               a)
             a))


ACL2 Error [Translate] in ( DEFUN SWAP-UPPER-1-LOWER-2 ...):  It is
illegal to call UPDATE-UPPERI because it is a stobj updater or accessor
for a field of stobj type.  For a way to generate such a call, see
:DOC stobj-let.  Note:  this error occurred in the context 
(UPDATE-UPPERI 1 ROWPRIME A).
|#

; Here, finally, is a successful definition.  Note that unlike the second
; attempt above, it does not update the stobj a in the consumer (which is the
; last argument to stobj-let, i.e., a itself).  Rather, a is updated implicitly
; when the producer -- i.e., the call of swap-stobjs -- updates the two
; specified rows.

(defun swap-upper-1-lower-2 (a)
  (declare (xargs :stobjs (a)
                  :verify-guards nil))
  (stobj-let ((row (upperi 1 a))
              (rowprime (loweri 2 a)))
             (row rowprime)
             (swap-stobjs row rowprime)
             a))

; Below is a test, including initialization and printing code.

(defun init-coeffs (n row)
; Put n in every position of row.
  (declare (xargs :stobjs row)
           (type double-float n))
  (let* ((row (update-coefsi 0 n row))
         (row (update-coefsi 1 n row))
         (row (update-coefsi 2 n row))
         (row (update-coefsi 3 n row)))
    row))

(defun init-lower (n a)
; Put n in every position of lower row n of a.
  (declare (xargs :stobjs a
                  :guard (member n '(0 1 2 3))))
  (stobj-let ((row (loweri n a)))
             (row)
             (init-coeffs (to-df n) row)
             a))

(defun init-upper (n a)
; Put n+10 in every position of upper row n of a.
  (declare (xargs :stobjs a
                  :guard (member n '(0 1 2 3))))
  (stobj-let ((row (upperi n a)))
             (row)
             (init-coeffs (to-df (+ n 10)) row)
             a))

(defun init-a (a)
; For n from 0 to 3, put n in every position of lower row n of a.
; For n from 0 to 3, put n+10 in every position of upper row n of a.
  (declare (xargs :stobjs a))
  (let* ((a (init-lower 0 a))
         (a (init-lower 1 a))
         (a (init-lower 2 a))
         (a (init-lower 3 a))
         (a (init-upper 0 a))
         (a (init-upper 1 a))
         (a (init-upper 2 a))
         (a (init-upper 3 a)))
    a))

(defun coefs-to-list (row)
; Represent the given row as a list of its entries, in order.
  (declare (xargs :stobjs row))
  (list (from-df (coefsi 0 row))
        (from-df (coefsi 1 row))
        (from-df (coefsi 2 row))
        (from-df (coefsi 3 row))))

(defun upper-to-list (n a)
; Represent the nth upper row of a as a list of its entries, in order.
  (declare (xargs :stobjs a
                  :guard (member n '(0 1 2 3))))
  (stobj-let ((row (upperi n a)))
             (lst)
             (coefs-to-list row )
             lst))

(defun lower-to-list (n a)
; Represent the nth lower row of a as a list of its entries, in order.
  (declare (xargs :stobjs a
                  :guard (member n '(0 1 2 3))))
  (stobj-let ((row (loweri n a)))
             (lst)
             (coefs-to-list row )
             lst))

(defun A-to-list (a)
; Display a as a matrix in an obvious list form.
  (declare (xargs :stobjs a))
  (list 'a
        :lower
        (list (lower-to-list 0 a)
              (lower-to-list 1 a)
              (lower-to-list 2 a)
              (lower-to-list 3 a))
        :upper
        (list (upper-to-list 0 a)
              (upper-to-list 1 a)
              (upper-to-list 2 a)
              (upper-to-list 3 a))))

; Now for some experiments....

; All zeros:
(assert-event
 (equal (a-to-list a)
        '(A :LOWER ((0 0 0 0)
                    (0 0 0 0)
                    (0 0 0 0)
                    (0 0 0 0))
            :UPPER ((0 0 0 0)
                    (0 0 0 0)
                    (0 0 0 0)
                    (0 0 0 0)))))

; We use value-triple here so that we can call init-a, not because we care
; about the value returned by evaluating that call.
(value-triple (init-a a)
              :stobjs-out '(a))

; Result is shown just below:
(assert-event
 (equal (a-to-list a)
        '(A :LOWER ((0 0 0 0)
                    (1 1 1 1)
                    (2 2 2 2)
                    (3 3 3 3))
            :UPPER ((10 10 10 10)
                    (11 11 11 11)
                    (12 12 12 12)
                    (13 13 13 13)))))

; We use value-triple here so that we can call swap-upper-1-lower-2, not
; because we care about the value returned by evaluating that call.
(value-triple (swap-upper-1-lower-2 a)
              :stobjs-out '(a))

; Result is shown just below, where we see that row 2 of lower
; was swapped with row 1 of upper.
(assert-event
 (equal (a-to-list a)
        '(A :LOWER ((0 0 0 0)
                    (1 1 1 1)
                    (11 11 11 11)
                    (3 3 3 3))
            :UPPER ((10 10 10 10)
                    (2 2 2 2)
                    (12 12 12 12)
                    (13 13 13 13)))))

