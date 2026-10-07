; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.  The fix was to essentially to stop removing guard-holders from
; the compiled lambda cache (see :DOC print-cl-cache).

; Finding 35: EC-CALL inside a quoted LAMBDA object is COMPILED AWAY, so the
; compiled cl-cache code calls the raw function directly, never entering *1*.
;
; Three cooperating source facts:
;   (1) guard-clauses, history-management.lisp:13999-14010, emits guard
;       obligations for (return-last 'ec-call1-raw ign (fn a1 ... ak)) only for
;       the ARGS, with the comment "Since (return-last 'ec-call1-raw ign
;       (fn arg1 ... argk)) leads to the call (*1*fn arg1 ... argk) ... in raw
;       Common Lisp, we need only verify guards for the argi."  So the lambda
;       object's guard comes out 'T.  That premise is FALSE for the
;       compiled-lambda path.
;   (2) all-fnnames1-exec, defuns.lisp:4231-4235, collects only
;       (fargs (fargn x 3)) for the ec-call1-raw case -- never FN.  So neither
;       chk-common-lisp-compliant-subfunctions-cmp (defuns.lisp:4260) nor
;       maybe-re-validate-cl-cache-line (apply-raw.lisp:1345-1360) sees FN, and
;       the cache line is judged compliant.
;   (3) logic-code-to-runnable-code, defuns.lisp:9219-9221, is
;         ((eq (ffn-symb term) 'return-last)
;          (logic-code-to-runnable-code nil (fargn term 3) wrld))
;       -- it descends into arg 3 and DISCARDS the ec-call wrapper, as does
;       remove-guard-holders.  make-compileable-guard-and-body-lambdas
;       (defuns.lisp:9379) therefore compiles a bare call, run by apply$-lambda
;       (apply-raw.lisp:4168-4207) after checking only the guard 'T.
;
; The value discrepancy: nonnegative-integer-quotient is in
; *initial-logic-fns-with-raw-code* (axioms.lisp:14502) with raw code (floor i j).
; Logically (nonnegative-integer-quotient -5 2) = 0 (the (< (ifix i) j) base case
; fires); raw (floor -5 2) = -3.  The lift to a proof of nil is ev-fncall-meta
; (rewrite.lisp:12559-12588), which for a :common-lisp-compliant metafunction
; calls ev-fncall! -- literally (mv nil (apply fn args) nil) in raw Lisp
; (rewrite.lisp:12545), with *aokp* non-nil, so the cl-cache shortcut is live.
;
; Two controls isolate it exactly: without the EC-CALL the lambda's real guard
; obligation appears and DEFUN MYMETA fails guard verification; with lambda$
; instead of a quoted LAMBDA the authenticated path compiles the real ec-call and
; raw evaluation agrees with the logic.  See also new-54 for the memory-unsafety
; and program-only consequences of the same root cause.
; FIX: special-case ec-call1-raw in logic-code-to-runnable-code so it re-emits
; (ec-call ...) (or (*1*fn ...)) rather than a bare call.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)
; Matt K. mod: The must-fail was originally around the entire encapsulate, but
; I have placed it where the first failure is expected to occur.  With the two
; must-fail wrappers omitted below, this encapsulate is admitted in ACL2
; Version 8.7 and also in github versions through the end of September, 2026.
(encapsulate ()
  (defconst *ec-bad-lam*
    '(lambda (y)
; Matt K. mod: Originally Claude had '(nonnegative-integer-quotient) in place
; of 'nil below.  But even with 'nil, where the return-last call isn't
; malformed for ec-call, there was a bug.  The fix makes even this more benign
; version fail below, as it should.
       (return-last 'ec-call1-raw 'nil
                    (nonnegative-integer-quotient y '2))))
  (defun ectarget () nil)
  (defun ecmeta (x)
    (declare (xargs :guard (pseudo-termp x)))
    (if (equal x '(ectarget))
        (if (equal (apply$ *ec-bad-lam* '(-5)) 0) ; logic 0, raw -3
            (list 'quote nil)
          (list 'quote t))
      x))
  (defevaluator ecevl ecevl-lst ((ectarget)))
  (defthm ecmeta-correct
    (implies (and (pseudo-termp x) (alistp a))
             (equal (ecevl x a) (ecevl (ecmeta x) a)))
    :hints (("Goal" :in-theory (enable (:executable-counterpart apply$)
                                       (:executable-counterpart apply$-lambda)
                                       (:executable-counterpart ev$))))
    :rule-classes ((:meta :trigger-fns (ectarget))))
  (must-fail
   (defthm ec-bad (equal (ectarget) t) :rule-classes nil
     :hints (("Goal" :in-theory (disable (:definition ectarget)
                                         (:executable-counterpart ectarget)))))
   )
  (in-theory (disable ecmeta-correct))
  (must-fail
   (defthm ec-nil nil :rule-classes nil :hints (("Goal" :use ec-bad)))
   ))
