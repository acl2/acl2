; Defabsstobj Example 4
; Copyright (C) 2012, Regents of the University of Texas
; Written by Matt Kaufmann, Dec., 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This example is closely based on an example from Sol Swords that showed the
; unsoundness of abstract stobjs in ACL2 Version 5.0, and led to the
; development of the :PROTECT keyword of defabsstobj.

; This book needs a ttag.

(in-package "ACL2")

(defstobj st$c fld$c) ; initially has fld$c = nil

(defstub stop () nil)

(defun update-fld-nil-good$c (st$c)
  (declare (xargs :stobjs st$c))
  (update-fld$c nil st$c))

(defun update-fld-nil-bad$c (st$c)
  (declare (xargs :stobjs st$c))
  (let ((st$c (update-fld$c t st$c)))
    (prog2$ (stop) ; aborts
            (update-fld$c nil st$c))))

(defun st$ap (x)
  (declare (xargs :guard t))
  (equal x nil))

(defun create-st$a ()
  (declare (xargs :guard t))
  nil)

(defun fld$a (st$a)
  (declare (xargs :guard t))
  st$a)

(defun update-fld-nil-bad$a (st$a)
  (declare (xargs :guard t)
           (ignore st$a))
  nil)

(defun update-fld-nil-good$a (st$a)
  (declare (xargs :guard t)
           (ignore st$a))
  nil)

(defun-nx st$corr (st$c x)
  (and (st$ap x)
       (st$cp st$c)
       (equal (fld$c st$c) nil)))

(in-theory (disable (st$corr)))

(DEFTHM CREATE-ST{CORRESPONDENCE}
        (ST$CORR (CREATE-ST$C) (CREATE-ST$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-ST{PRESERVED}
        (ST$AP (CREATE-ST$A))
        :RULE-CLASSES NIL)

(DEFTHM FLD{CORRESPONDENCE}
        (IMPLIES (ST$CORR ST$C ST)
                 (EQUAL (FLD$C ST$C) (FLD$A ST)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD-NIL-GOOD{CORRESPONDENCE}
        (IMPLIES (ST$CORR ST$C ST)
                 (ST$CORR (UPDATE-FLD-NIL-GOOD$C ST$C)
                          (UPDATE-FLD-NIL-GOOD$A ST)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD-NIL-GOOD{PRESERVED}
        (IMPLIES (ST$AP ST)
                 (ST$AP (UPDATE-FLD-NIL-GOOD$A ST)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD-NIL-BAD{CORRESPONDENCE}
        (IMPLIES (ST$CORR ST$C ST)
                 (ST$CORR (UPDATE-FLD-NIL-BAD$C ST$C)
                          (UPDATE-FLD-NIL-BAD$A ST)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD-NIL-BAD{PRESERVED}
        (IMPLIES (ST$AP ST)
                 (ST$AP (UPDATE-FLD-NIL-BAD$A ST)))
        :RULE-CLASSES NIL)

(defabsstobj st
  :exports ((fld)
            (update-fld-nil-good)
            (update-fld-nil-bad :protect t)))

(defmacro restore-state ()

; With a trust tag, we cheat to restore the state.  Upon request we may provide
; a utility, to be executed without a trust tag, that restores the abstract
; stobj to its initial value and resets the state to a non-error state.

  `(progn
     (defttag :restore-state)
     (remove-untouchable illegal-to-certify-message nil)
     (local (value-triple

; We use a special value for the first argument of set-absstobj-debug, namely
; :reset, in order to reset the part of the state that indicates an invariance
; violation for the abstract stobj, as though an error had not occurred.  That
; value requires an active trust tag and also requires :always to be true.

             (set-absstobj-debug :reset
                                 :event-p nil
                                 :always t)))
     (make-event (er-progn (assign illegal-to-certify-message nil)
                           (trans-eval '(update-fld-nil-good st) 'top state t)
                           (value '(value-triple nil))))
     (push-untouchable illegal-to-certify-message nil)
     (defttag nil)))

(make-event
 (mv-let
  (erp val state)
  (trans-eval '(update-fld-nil-bad st) 'top state t)

; The above causes the following error:

;   ACL2 Error in CHK-ABSSTOBJ-INVARIANTS:  Possible invariance violation
;   for an abstract stobj!  See :DOC set-absstobj-debug, and PROCEED AT
;   YOUR OWN RISK.

  (declare (ignore erp val))
  (value '(value-triple :irrelevant-value))))

; An error now occurs when LDing this file.  Reset the state, but first, let's
; check that we are in a bad state: even though (st$ap st) is always intended
; to hold, and hence logically (fld st) = (fld$a st) = nil, nevertheless (fld
; st) computes to t.
(assert-event (equal (fld st) t))
(restore-state)
(assert-event (equal (fld st) nil))

; Let's set things up to get a more informative error message:
(local (set-absstobj-debug t))

(make-event
 (mv-let
  (erp val state)
  (trans-eval '(update-fld-nil-bad st) 'top state t)

; The above causes the following error:

;   ACL2 Error in CHK-ABSSTOBJ-INVARIANTS:  Possible invariance violation
;   for an abstract stobj!  See :DOC set-absstobj-debug, and PROCEED AT
;   YOUR OWN RISK.  Evaluation was aborted under a call of abstract stobj
;   export UPDATE-FLD-NIL-BAD.

  (declare (ignore erp val))
  (value '(value-triple :irrelevant-value))))

; Restore the state at the end, so that this book will certify (with a trust
; tag).
(restore-state)
