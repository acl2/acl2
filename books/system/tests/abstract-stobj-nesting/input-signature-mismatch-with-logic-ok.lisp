; Copyright (C) 2021, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; In ACL2 Version 8.3 and into May 2021, the final defabsstobj event below
; failed because of an input signature mismatch between the :logic and :exec
; functions.  That check was too aggressive, as pointed out by Sol Swords;
; now, that final event is admitted.

(in-package "ACL2")

(defstobj st2$c (fld2 :type (array t (8))))

(defun st2$ap (x)
  (declare (xargs :guard t))
  (declare (ignore x))
  t)

(defun create-st2$a ()
  (declare (xargs :guard t))
  nil)

(defun st2$corr (st2$c st2$a)
  (declare (xargs :stobjs st2$c
                  :guard t))
  (declare (ignore st2$c st2$a))
  t)

(defun bad$a (x y st2$a)
  (declare (xargs :guard (and (natp x) (< x 8))))
  (mv x (and y st2$a nil)))

(defun bad$c (x y st2$c)
  (declare (xargs :stobjs st2$c
                  :guard (and (natp x) (< x 8))))
  (let ((st2$c (update-fld2i x y st2$c)))
    (mv x st2$c)))

(progn

(DEFTHM CREATE-ST2{CORRESPONDENCE}
        (ST2$CORR (CREATE-ST2$C) (CREATE-ST2$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-ST2{PRESERVED}
        (ST2$AP (CREATE-ST2$A))
        :RULE-CLASSES NIL)

(DEFTHM BAD{CORRESPONDENCE}
        (IMPLIES (AND (ST2$CORR ST2$C ST2)
                      (NATP X)
                      (< X 8))
                 (LET ((LHS (BAD$C X Y ST2$C))
                       (RHS (BAD$A X Y ST2)))
                      (AND (EQUAL (MV-NTH 0 LHS) (MV-NTH 0 RHS))
                           (ST2$CORR (MV-NTH 1 LHS)
                                     (MV-NTH 1 RHS)))))
        :RULE-CLASSES NIL)

(DEFTHM BAD{PRESERVED}
        (IMPLIES (AND (ST2$AP ST2) (NATP X) (< X 8))
                 (ST2$AP (MV-NTH 1 (BAD$A X Y ST2))))
        :RULE-CLASSES NIL)
)

(defabsstobj st2
  :exports ((bad :logic bad$a :exec bad$c)))

(assert-event (getpropc 'bad 'invariant-risk))
