; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book illustrates a successful use of swap-stobjs on stobj fields of an
; abstract stobj.

(in-package "ACL2")

(include-book "two-ordered-nums-stobj")

(make-event (er-progn
             (trans-eval '(update-two-ordered-nums 3 5 two-ordered-nums)
                         'my-top state nil)
             (value '(value-triple :updated))))

(assert-event (equal (fields-of-two-ordered-nums two-ordered-nums)
                     '(:N 3 :N2 5 :VALID T)))

(defun foo (two-ordered-nums)
  (declare (xargs :stobjs two-ordered-nums))
  (let ((two-ordered-nums (update-uenvalid nil two-ordered-nums)))
    (stobj-let ((n$ (uenslot1 two-ordered-nums))
                (n$2 (uenslot2 two-ordered-nums)))
               (n$ n$2)
               (mv-let (n$ n$2)
                 (swap-stobjs n$ n$2)
                 (let* ((n$ (update-n$val 0 n$))
                        (n$2 (if (posp (n$val n$2))
                                 n$2
                               (update-n$val 1 n$2))))
                   (mv n$ n$2)))
               (update-uenvalid t two-ordered-nums))))

(make-event (er-progn
             (trans-eval '(foo two-ordered-nums)
                         'my-top state nil)
             (value '(value-triple :swapped-and-updated))))

(assert-event (equal (fields-of-two-ordered-nums two-ordered-nums)
                     '(:N 0 :N2 3 :VALID T)))
