; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book tests that when a generic stobj st is given an attachment, that
; attachment is used even when st is (the type of) a field of a concrete stobj.

(in-package "ACL2")

(include-book "impl")

(include-book "nested-support")

; With the stobj attachment in place, time there are no errors when we
; evaluate.

(value-triple (f1 top1))
(value-triple (f2 top2))
(value-triple (f2-caller top2))
(value-triple (g1 top1))
(value-triple (g2 top2))
(value-triple (g2-caller top2))

; Now we replicate what's in the sub-book, but with new names, to see that
; evaluation works as expected even when functions are defined in the present
; book.

(defun f1a (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((st (st1 top1))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun f1a-caller (top1)
  (declare (xargs :stobjs top1))
  (f1a top1))

(defun-inline g1a (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((st (st1 top1))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun g1a-caller (top1)
  (declare (xargs :stobjs top1))
  (g1a top1))

(defun f2a (top2)
  (declare (xargs :stobjs top2))
  (stobj-let
   ((st (st2 top2))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun f2a-caller (top2)
  (declare (xargs :stobjs top2))
  (f2a top2))

(defun-inline g2a (top2)
  (declare (xargs :stobjs top2))
  (stobj-let
   ((st (st2 top2))) ; bindings
   (val)             ; producer variable(s)
   (misc st)         ; producer
   val))

(defun g2a-caller (top2)
  (declare (xargs :stobjs top2))
  (g2a top2))

(local (include-book "std/testing/must-fail" :dir :system))
(value-triple (f1a top1))
(value-triple (f2a top2))
(value-triple (f2a-caller top2))
(value-triple (g1a top1))
(value-triple (g2a top2))
(value-triple (g2a-caller top2))

