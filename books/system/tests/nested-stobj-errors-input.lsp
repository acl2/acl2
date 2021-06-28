; Copyright (C) 2021, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; For more tests of stobj-let, see also the community books file and directory
; system/tests/nested-stobj-tests.lisp and
; system/tests/abstract-stobj-nesting/.

(defstobj sub1 sub1-fld1)
(defstobj top1 (top1-fld :type sub1) :renaming ((update-top1-fld !top1-fld)))

; Error: bad implicit updater for producer variable
(defun f1 (x top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (sub1)
   (update-sub1-fld1 x sub1)
   top1))

; Error: bad explicit updater for producer variable
(defun f1 (x top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1) update-top1-fld))
   (sub1)
   (update-sub1-fld1 x sub1)
   top1))

; Error: bad explicit updater for non-producer variable
(defun f1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1) update-top1-fld))
   (val)
   (sub1-fld1 sub1)
   val))

; No error, even though implicit updater is wrong, because it doesn't
; correspond to a producer variable.
(defun f1 (top1)
  (declare (xargs :stobjs top1))
  (stobj-let
   ((sub1 (top1-fld top1)))
   (val)
   (sub1-fld1 sub1)
   val))
