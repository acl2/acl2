; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.  See also ec-call-in-quoted-lambda.lisp, which is really about
; the same bug.

; Finding 35, the non-nil consequences.  Because EC-CALL inside a quoted LAMBDA is
; compiled away (root cause in new-53), the compiled cl-cache code calls the RAW
; function and never enters *1* at all -- so three separate protections that live
; in *1* code are bypassed simultaneously.
;
; (a) INVARIANT-RISK: an arbitrary out-of-bounds heap write at DEFAULT
;     guard-checking.  aset1's raw code (axioms.lisp:13603-13605) is
;     (setf (svref (the simple-vector ar) n) val) with no bounds check.  Below,
;     magic-ev-fncall of (aset1 'ar *arr* 100 'zzz) on a DIMENSION-5 array is
;     correctly refused (erp = T), while the same call inside an ec-call'd quoted
;     lambda returns normally -- i.e. it wrote 95 slots past the end of a length-6
;     vector.  This is strictly worse than N45: no loop$/lambda$ trick is needed to
;     defeat put-invariant-risk, because invariant-risk only ever affects *1* code.
;
; (b) PROGRAM-ONLY: raw code with no logical counterpart runs.
;     (apply$ 'fchecksum-atom '(17)) is correctly refused --
;     "HARD ACL2 ERROR in PROGRAM-ONLY: The call (FCHECKSUM-ATOM 17) is an illegal
;     call of a function that has been marked as ``program-only'' ... and safe-mode
;     is active" -- because raw-apply-for-badged-fn (apply-raw.lisp:391-404) binds
;     safe-mode for :program-mode fn.  Inside an ec-call'd quoted lambda the same
;     call returns 262968298.  fail_program-only (interface-raw.lisp:2304-2341) is
;     unreachable because *1* is never entered.
;
; (c) :PROGRAM-mode guard protection, likewise (b2.lisp in the bundle).
;
; Together these break the guarantee stated, with its own warning, at
; interface-raw.lisp:2117-2119 and justified at defuns.lisp:8245: "This function
; guarantees that a call of a :logic mode function cannot lead to a call of a
; :program mode function ... So be careful when considering a relaxation of this
; guarantee!"
; FIX: see new-53.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
(include-book "projects/apply/top" :dir :system)

(defconst *ec-arr*
  (compress1 'ar (list (list :header :dimensions '(5)
                             :maximum-length 11 :default 0 :name 'ar))))

; The ordinary route is protected.
(assert-event (mv-let (erp val)
                (magic-ev-fncall 'aset1 (list 'ar *ec-arr* 100 'zzz) state t nil)
                (declare (ignore val))
                erp))

; (a) ... but the ec-call'd quoted lambda writes out of bounds.
(must-fail
 (assert-event
  (consp (apply$ '(lambda (a i) (return-last 'ec-call1-raw '(aset1)
                                             (aset1 'ar a i 'zzz)))
                 (list *ec-arr* 100)))))

; (b) ... and program-only raw code runs.
(defbadge fchecksum-atom)
(must-fail
 (assert-event
  (integerp (apply$ '(lambda (y) (return-last 'ec-call1-raw '(fchecksum-atom)
                                              (fchecksum-atom y)))
                    '(17)))))
