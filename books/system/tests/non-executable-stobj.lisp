; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; These are tests of defstobj specifying keyword :non-executable t.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

;;; Basics

(defstobj st1 fld1 :non-executable t)

(must-fail (fld1 st1)
           :expected :hard)

(must-fail (update-fld1 3 st1)
           :expected :hard)

;;; Congruent to non-executable

(defstobj st2 fld2 :congruent-to st1)

(make-event
 (er-progn (trans-eval-no-warning '(update-fld1 4 st2) 'top state nil)
           (value '(assert-event (equal (fld1 st2) 4))))
 :check-expansion t)

;;; With-local-stobj based on non-executable

(defstobj top
  (st1-fld :type st1)
  st2-fld)

(defun foo (x top)
  (declare (xargs :stobjs top))
  (stobj-let
   ((st1 (st1-fld top)))        ; bindings
   (st1)                        ; producer variable(s)
   (update-fld1 x st1)          ; producer
   top))

(defun bar (top)
  (declare (xargs :stobjs top))
  (stobj-let
   ((st1 (st1-fld top))) ; bindings
   (val)                 ; producer variable(s)
   (fld1 st1)            ; producer
   val))

(make-event
 (er-progn (trans-eval-no-warning '(foo 7 top) 'top state nil)
           (value '(assert-event (equal (bar top) 7))))
 :check-expansion t)

;;; Abstract stobj based on non-executable

(defun st1$ap (x)
  (declare (xargs :guard t))
  (and (consp x)
       (null (cdr x))))

(defun create-st1$a ()
  (declare (xargs :guard t))
  '(nil))

(defun fld1$a (x)
  (declare (xargs :guard (st1$ap x)))
  (car x))

(defun update-fld1$a (a x)
  (declare (xargs :guard (st1$ap x)))
  (declare (ignore x))
  (list a))

(DEFTHM CREATE-ST1-ABS{CORRESPONDENCE}
        (EQUAL (CREATE-ST1) (CREATE-ST1$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-ST1-ABS{PRESERVED}
        (ST1$AP (CREATE-ST1$A))
        :RULE-CLASSES NIL)

(DEFTHM FLD1-ABS{CORRESPONDENCE}
        (IMPLIES (AND (EQUAL ST1 ST1-ABS)
                      (ST1$AP ST1-ABS))
                 (EQUAL (FLD1 ST1) (FLD1$A ST1-ABS)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD1-ABS{CORRESPONDENCE}
        (IMPLIES (AND (EQUAL ST1 ST1-ABS)
                      (ST1$AP ST1-ABS))
                 (EQUAL (UPDATE-FLD1 V ST1)
                        (UPDATE-FLD1$A V ST1-ABS)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD1-ABS{PRESERVED}
        (IMPLIES (ST1$AP ST1-ABS)
                 (ST1$AP (UPDATE-FLD1$A V ST1-ABS)))
        :RULE-CLASSES NIL)

(defabsstobj st1-abs
  :foundation st1
  :recognizer (st1-absp :logic st1$ap :exec st1p)
  :creator (create-st1-abs :logic create-st1$a :exec create-st1)
  :corr-fn equal
  :exports ((fld1-abs :logic fld1$a :exec fld1)
            (update-fld1-abs :logic update-fld1$a :exec update-fld1)))

(make-event
 (er-progn (trans-eval-no-warning '(update-fld1-abs 10 st1-abs) 'top state nil)
           (value '(assert-event (equal (fld1-abs st1-abs) 10))))
 :check-expansion t)

;;; Memory test

; In 64-bit LispWorks, constant array-dimension-limit has value (1- (expt 2
; 29)) = 536870911.  The implementation of defstobj checks that the size of an
; array field is strictly less than this number.  We thus make the test below
; depend on the Lisp, with a robust test for all Lisps besides LispWorks.
; This event is local to support compilation for multiple Lisps by setting
; "make" variable ACL2_COMP=1.
(local
 (defstobj big ; maybe too big by far if executable
   (ar :type (array t (#+lispworks
                       536870910
                       #-lispworks
                       100000000000)))
   :non-executable t))

;;; Redundancy

(must-fail (defstobj st1 fld1))

(defstobj st3 fld3)

(must-fail (defstobj st3 fld3 :non-executable t))

; The following fails too, only because we now require syntactic identity for
; defstobj redundancy.
(must-fail (defstobj st3 fld3 :non-executable nil))

(defstobj st4 fld4 :non-executable t)

(must-fail (defstobj st4 fld4))
