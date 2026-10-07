; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; N73: DEFABSSTOBJ's :PROTECT enumeration does not follow congruent stobjs, so an
; :EXEC that makes two updates through a CONGRUENT stobj's updaters is counted as
; making ZERO updates and :PROTECT T is not demanded.
;
; fn-stobj-updates-p (other-events.lisp:22778), stobj-updates-p (:22801) and
; unprotected-export-p (:22886) test
;     (member-eq st (stobjs-out (ffn-symb term) wrld))
; against the STATIC 'stobjs-out property, which for a congruent stobj's updater
; names the CONGRUENT stobj (ST$C2), not the foundation (ST$C).  Measured: two
; functions making the identical pair of updates give
;   :TWO-UPD T  :TWO-UPD-CONG NIL  :UNPROT-TWO T  :UNPROT-CONG NIL
; The non-congruent version is correctly rejected with "The :EXEC field SET$C ...
; appears capable of modifying the foundational stobj, ST$C, non-atomically; yet
; :PROTECT T was not specified"; the congruent version below certifies.
;
; Consequence, verified: after including such a book, a top-level (setv 99 st)
; interrupted mid-update leaves (geta st) = 99 and (getb st) = 0, while
; (equal (geta st) (getb st)) is a certified theorem of that book, with no ttag
; and no illegal-state detection.  NOT a proof of nil: the corruption is only
; observable across a non-local exit, and inside a book the prover can only
; evaluate abstract stobjs created by with-local-stobj, which calls the creator
; freshly every time (basis-a.lisp:9701 -- no pooling), so a partially updated
; stobj dies with the aborted evaluation.  hard-error returns nil rather than
; exiting during proofs, and the :EXEC's guard is discharged by the {GUARD-THM}
; obligation, so a guard violation cannot exit either.
; FIX: resolve congruent stobjs to their foundation before the stobjs-out test.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; DEFECT DEMO: the :PROTECT enumeration (stobj-updates-p / unprotected-export-p,
; other-events.lisp:22778-22895) does not follow congruent stobjs, so an :EXEC
; function that updates the foundational stobj TWICE through a congruent stobj's
; updaters is judged atomic and :PROTECT T is not required.

(defstobj st$c (a$c :type (integer 0 *) :initially 0)
               (b$c :type (integer 0 *) :initially 0))

(defstobj st$c2 (a$c2 :type (integer 0 *) :initially 0)
                (b$c2 :type (integer 0 *) :initially 0)
  :congruent-to st$c)

(defun st$ap (x) (declare (xargs :guard t)) (natp x))
(defun create-st$a () (declare (xargs :guard t)) 0)
(defun get$a (st) (declare (xargs :guard (st$ap st))) st)
(defun set$a (v st) (declare (xargs :guard (and (natp v) (st$ap st))) (ignore st)) v)

(defun st$corr (st$c st)
  (declare (xargs :stobjs st$c :guard t))
  (and (st$cp st$c) (natp st) (equal (a$c st$c) st) (equal (b$c st$c) st)))

(defun geta$c (st$c) (declare (xargs :stobjs st$c)) (a$c st$c))
(defun getb$c (st$c) (declare (xargs :stobjs st$c)) (b$c st$c))

; Two updates of st$c, via the CONGRUENT stobj st$c2's updaters, with a
; non-local exit possible in between.
(defun set$c (v st$c)
  (declare (xargs :stobjs st$c :guard (natp v)))
  (let* ((st$c (update-a$c2 v st$c)))
    (prog2$ (and (eql v 99) (hard-error 'set$c "interrupted mid-update" nil))
            (update-b$c2 v st$c))))

(DEFTHM CREATE-ST{CORRESPONDENCE} (ST$CORR (CREATE-ST$C) (CREATE-ST$A))
  :rule-classes nil)
(DEFTHM CREATE-ST{PRESERVED} (ST$AP (CREATE-ST$A)) :rule-classes nil)
(DEFTHM GETA{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST) (ST$AP ST)) (EQUAL (GETA$C ST$C) (GET$A ST)))
  :rule-classes nil)
(DEFTHM GETB{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST) (ST$AP ST)) (EQUAL (GETB$C ST$C) (GET$A ST)))
  :rule-classes nil)
(DEFTHM SETV{CORRESPONDENCE}
  (IMPLIES (AND (ST$CORR ST$C ST) (NATP V) (ST$AP ST))
           (ST$CORR (SET$C V ST$C) (SET$A V ST)))
  :rule-classes nil)
(DEFTHM SETV{PRESERVED}
  (IMPLIES (AND (NATP V) (ST$AP ST)) (ST$AP (SET$A V ST)))
  :rule-classes nil)

; Accepted with NO :PROTECT T for SETV, even though SET$C is non-atomic.

(must-fail
(defabsstobj st
  :foundation st$c
  :recognizer (stp :logic st$ap :exec st$cp)
  :creator (create-st :logic create-st$a :exec create-st$c)
  :corr-fn st$corr
  :exports ((geta :logic get$a :exec geta$c)
            (getb :logic get$a :exec getb$c)
            (setv :logic set$a :exec set$c))))

; Added by Matt K.  Before the bug fix, and with the must-fail fwrappers above
; and below removed, the following event went through.  I suspect that a proof
; of nil could have been obtained by suitable use of a clause-processor, but I
; didn't try.

(must-fail
(progn

(thm (implies (stp st) (equal (geta st) (getb st))))

(must-fail (setv 99 st) ; hard error
           :expected :hard)

(assert-event (not (implies (stp st) (equal (geta st) (getb st)))))
)
)
