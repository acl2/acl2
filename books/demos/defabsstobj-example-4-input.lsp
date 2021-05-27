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

; Error: illegal state
(+ 3 4)

:continue-from-illegal-state

; No longer an error
(+ 3 4)

; An error now occurs when LDing this file.  Reset the state, but first, let's
; check that we are in a bad state: even though (st$ap st) is always intended
; to hold, and hence logically (fld st) = (fld$a st) = nil, nevertheless (fld
; st) computes to t.
(assert-event (equal (fld st) t))

; Retore the state:
(make-event
 (mv-let
  (erp val state)
  (trans-eval '(update-fld-nil-good st) 'top state t)
  (declare (ignore erp val))
  (value '(value-triple :irrelevant-value))))

(assert-event (equal (fld st) nil))

; Let's set things up to get a more informative error message:
(local (set-absstobj-debug t))

; Again:
(make-event
 (mv-let
  (erp val state)
  (trans-eval '(update-fld-nil-bad st) 'top state t)
  (declare (ignore erp val))
  (value '(value-triple :irrelevant-value))))

(continue-from-illegal-state)

;;;;;; !! new

(with-output
  :off :all
  (defevaluator evl evl-list
    ((equal x y))))

(defun simple-cl-proc (cl term st)
  (declare (xargs :stobjs st)
           (ignore term))
  (let ((st (update-fld-nil-bad st)))
    (mv nil (list cl) st)))

(defthm correctness-of-simple-cl-proc
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl (conjoin-clauses
                      (clauses-result (simple-cl-proc cl term st)))
                     a))
           (evl (disjoin cl) a))
  :rule-classes :clause-processor)

(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (thm (equal x x)
      :hints (("Goal" :clause-processor simple-cl-proc))))

(continue-from-illegal-state)

(with-output :off error ; avoid discrepancy between ACL2 and ACL2(p)
  (thm (equal x x)
       :hints (("Goal"
                :instructions ((cl-proc :function simple-cl-proc :hint nil))))))

(continue-from-illegal-state)

; Use a trust tag to avoid certification failure.

(defttag :bogus-cert)
(remove-untouchable illegal-to-certify-message nil)
(make-event (pprogn (f-put-global 'illegal-to-certify-message nil state)
                    (value '(value-triple :certification-made-ok))))
(defttag nil)

(value-triple "Completed")
