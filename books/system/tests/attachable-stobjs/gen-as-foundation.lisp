; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; We define an abstract stobj (not attachable) st-top that has an attachable
; stobj st as a foundation.  Export misc-top of st-top is defined to be export
; misc of st, which causes an error.  But in gen-as-foundation-test.lisp, we
; see that by attaching an implementation to st for which misc does not cause
; an error, we avoid an error with misc-top as well -- as expected.

(in-package "ACL2")

; Introduce attachable stobj st:
(include-book "gen")

(defun-nx st-top-corr (x y)
  (equal x y))

(DEFTHM CREATE-ST-TOP{CORRESPONDENCE}
  (ST-TOP-CORR (CREATE-ST) (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-ST-TOP{PRESERVED}
  (ST$AP (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM MISC-TOP{CORRESPONDENCE}
  (IMPLIES (AND (ST-TOP-CORR ST ST-TOP)
                (ST$AP ST-TOP))
           (EQUAL (MISC ST) (MISC$A ST-TOP)))
  :RULE-CLASSES NIL)

(defabsstobj st-top
  :foundation st
  :recognizer (st-topp :logic st$ap :exec stp)
  :creator (create-st-top :logic create-st$a :exec create-st)
  :corr-fn st-top-corr
  :exports ((misc-top :logic misc$a :exec misc)))

(defun f1-top (st-top)
  (declare (xargs :stobjs st-top))
  (misc-top st-top))

(local
 (progn
   (local (include-book "std/testing/must-fail" :dir :system))
   (must-fail (value-triple (f1-top st-top)))))
