; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See nested.lisp for comments.

(in-package "ACL2")

(include-book "gen")

(defstobj top1
  (st1 :type st))

(defun f1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((st (st1 top1))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun f1-caller (top1)
  (declare (xargs :stobjs top1))
  (f1 top1))

; For the following, function g1$inline is put into world global 'ext-gens by
; virtue of the call of misc in the body.
(defun-inline g1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((st (st1 top1))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun g1-caller (top1)
  (declare (xargs :stobjs top1))
  (g1 top1))

; Now we replicate what's above, but in the case that the concrete stobj
; declares :inline t.

(defstobj top2
  (st2 :type st)
  :inline t)

(defun f2 (top2)
  (declare (xargs :stobjs top2))
  (stobj-let
   ((st (st2 top2))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun f2-caller (top2)
  (declare (xargs :stobjs top2))
  (f2 top2))

; For the following, function g2$inline is put into world global 'ext-gens by
; virtue of the call of misc in the body.
(defun-inline g2 (top2)
  (declare (xargs :stobjs top2))
  (stobj-let
   ((st (st2 top2))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun g2-caller (top2)
  (declare (xargs :stobjs top2))
  (g2 top2))

; Test that the functions defined above cause errors, as expected, since
; generic stobj st (introduced in gen.lisp) has not been given an attachment.

(local (include-book "std/testing/must-fail" :dir :system))
(local (must-fail (value-triple (f1 top1))))
(local (must-fail (value-triple (f2 top2))))
(local (must-fail (value-triple (f2-caller top2))))
(local (must-fail (value-triple (g1 top1))))
(local (must-fail (value-triple (g2 top2))))
(local (must-fail (value-triple (g2-caller top2))))
