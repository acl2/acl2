; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "misc/eval" :dir :system)

(defstobj st1 fld1)
(defstobj st2 fld2 :congruent-to st1)
(defun foo (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (swap-stobjs st1 st2))

(defmacro my-eval (form)
  `(make-event
    (er-progn
     (trans-eval ',form 'top state nil)
     (value '(value-triple t)))))

(my-eval (update-fld1 3 st1))
(assert-event (equal (fld1 st1) 3))
(my-eval (update-fld2 4 st2))
(assert-event (equal (fld2 st2) 4))
(assert-event (equal (fld1 st1) 3))
(my-eval (foo st1 st2))
(assert-event (equal (fld2 st2) 3))
(assert-event (equal (fld1 st1) 4))
(my-eval (foo st2 st1))
(assert-event (equal (fld2 st2) 4))
(assert-event (equal (fld1 st1) 3))

(must-fail
; Error: Need to return the modified stobjs.
(defun bar (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (mv-let (st1 st2)
    (swap-stobjs st1 st2)
    (mv (fld1 st2) (fld2 st1))))
)

(defun bar (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (mv-let (st1 st2)
    (swap-stobjs st1 st2)
    (mv (fld1 st2) (fld2 st1) st1 st2)))

(my-eval (bar st1 st2)) ; should return (mv 3 4 ...).
(my-eval (bar st1 st2)) ; should return (mv 4 3 ...).
(my-eval (bar st1 st2)) ; should return (mv 3 4 ...).
(assert-event (equal (fld2 st2) 3))
(assert-event (equal (fld1 st1) 4))
