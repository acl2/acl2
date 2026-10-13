; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 57: the loop$-alist :TERM that raw Lisp runs INSIDE THE PROVER has its
; guard-holders stripped, so ec-call and mbe are discarded exactly as they were
; for quoted LAMBDA objects before c0fee4d67b.  Same bug shape, different call
; site, NOT fixed by that commit.
;
; convert-tagged-loop$s-to-pairs passes RRL = t at defuns.lisp:9632 (and the two
; consistency checks at :9674 and :9709 do the same), so
; logic-code-to-runnable-code replaces every return-last by its third argument.
; The raw loop$ macro (translate.lisp:18979) is
;     `(cond (*aokp* (loop ,@(remove-loop$-guards args)))
;            (t ,(or term ...)))      ; term = the loop$-alist :term
; -- the stripped term is what runs when *aokp* is NIL, which is the prover.
;
; Measured: the source (RETURN-LAST 'EC-CALL1-RAW 'NIL (FOO '-5)) is stored as
; (FOO '-5), so raw FOO is called instead of *1*FOO and FOO's guard is bypassed;
; guard-clauses generated obligations only for (fargs (fargn term 3)), i.e. for
; '-5, never for (natp -5).
;
; ISOLATION, all measured: the same loop$ WITHOUT ec-call is still refused ("The
; proof of the guard conjecture for HA has failed"); the same ec-call OUTSIDE a
; loop$ is sound (the prover proves the logical value and fails the raw one); and
; at the top level, where *aokp* is t and the real Lisp LOOP runs, the guard
; violation IS reported.  Only the *aokp*-nil branch is broken.
;
; An mbe variant works too: obligations are generated for the :exec branch while
; RRL = t keeps the :logic branch.
;
; FIX: pass RRL = nil at defuns.lisp:9632 (and :9674, :9709).  The comment inside
; logic-code-to-runnable-code explaining why guard-holders must survive applies
; here verbatim.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun foo (n)
  (declare (xargs :guard (natp n)))
  (mbe :logic (if (natp n) (list n) (list 99))
       :exec  (list n)))

(defun h ()
  (declare (xargs :guard t))
  (loop$ for x in (ec-call (foo -5)) collect x))

; THE DEFECT: inside a proof the stripped term calls raw FOO on -5.
(must-fail (defthm raw-value (equal (h) '(-5)) :rule-classes nil))

; The logical value, which must remain provable.
(defthm logical-value
  (equal (h) '(99))
  :hints (("Goal" :in-theory (disable (:executable-counterpart h))))
  :rule-classes nil)

; CONTROL: the same ec-call OUTSIDE a loop$ is handled correctly -- it goes
; through *1*foo and the logical value is what the prover sees.  This pins the
; loop$-alist path rather than ec-call in general.
(defun hc () (declare (xargs :guard t)) (ec-call (foo -5)))
(defthm control-outside-loop
  (equal (hc) '(99))
  :hints (("Goal" :in-theory (disable (:executable-counterpart hc))))
  :rule-classes nil)
(must-fail (defthm control-outside-loop-raw (equal (hc) '(-5)) :rule-classes nil))
