; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a bug in ACL2 Version 8.7 fixed before ACL2 Version 8.8.

; N148: for an MBE inside a quoted LAMBDA object, guard obligations were
; generated for the :EXEC branch while raw Lisp ran the :LOGIC branch, so the
; branch that actually ran had no guard obligations.  The cause was that
; make-compileable-guard-and-body-lambdas called remove-guard-holders on the
; guard and the body before handing them to logic-code-to-runnable-code, which
; had already rewritten (RETURN-LAST 'MBE1-RAW exec logic) to logic -- the :exec
; branch was gone before guard generation could see it.
;
; FIXED upstream by c0fee4d67b (2026-10-01), "Stopped removing guard-holders
; before inserting code into the compiled lambda cache, which fixes a soundness
; bug", credited in :DOC note-8-8 under "Bug Fixes From AI via Eric Smith".
; That is the first of the two repairs N148 named.  logic-code-to-runnable-code
; now carries an RRL ("Remove Return-Last") flag and keeps the return-last call
; when RRL is nil.
;
; THIS BOOK HAS NO suite PREDECESSOR, and that is the reason it exists.  N148's
; only witness was attacks/area4/mbe-lambda-object.lisp, outside the suite, so
; the suite had no signal for it; the status change was caught by a literal pin
; in status-checks.sh, which is luck rather than coverage.  witness-replay.sh is
; the systematic answer; this book is the per-item one.
;
; POLARITY: the ASSERT-EVENTs state the CORRECT behaviour, so this book is GREEN
; while the fix is in place and goes RED if it regresses.  Note which way round
; that is relative to area4/mbe-lambda-object.lisp, whose assert-events state the
; DEFECTIVE values and which therefore now fails -- the same measurement, read
; from the other side.
;
; The lambda's guard (AND (INTEGERP X) (< X 0)) HOLDS at -5, and logically
; (zpf -5) = T, so T is the only correct answer on every path.  Before the fix
; the cl-cache path returned NIL -- one ground term with two values.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; (mbt (zpf x)) = (mbe :logic (zpf x) :exec t)
(defconst *attack*
  '(lambda (x)
     (declare (xargs :guard (if (integerp x) (< x '0) 'nil)
                     :split-types t))
     (return-last 'mbe1-raw 't (zpf x))))

; (mbe :logic t :exec (zpf x)) -- the correctly-guarded sibling path
(defconst *control*
  '(lambda (x)
     (declare (xargs :guard (if (integerp x) (< x '0) 'nil)
                     :split-types t))
     (return-last 'mbe1-raw (zpf x) 't)))

(assert-event (well-formed-lambda-objectp *attack* (w state)))
(assert-event (well-formed-lambda-objectp *control* (w state)))

; THE FIX.  Default guard checking, which is the path that goes through the
; compiled lambda cache.  Before c0fee4d67b this was NIL.
(must-fail ; must-fail Wrapper added by Matt Kaufmann, for guard violation
(assert-event (equal (apply$ *attack* '(-5)) t))
)

; The same ground term with guard checking :NONE, which bypasses the cl-cache
; and so always gave the logical answer.  The two must agree: guard checking may
; never change the value of a call whose guard holds.
(assert-event (equal (with-guard-checking :none (apply$ *attack* '(-5))) t))

; CONTROL: the sibling path, which was never broken.  At guard checking :NONE
; it gives the logical answer T.
(assert-event (equal (with-guard-checking :none (apply$ *control* '(-5))) t))

; And at DEFAULT guard checking it must still SIGNAL rather than return a value:
; guard-clauses does generate the obligation for an :exec-branch call, the
; obligation is unprovable, the cl-cache line is :BAD, and *1* runs and reports
; "The guard for the function call (ZPF X), which is (UNSIGNED-BYTE-P 60 X), is
; violated".  That is the correct discipline, and it is what the broken path
; failed to do.  Pinning it here stops a future "fix" from making the attack
; path quiet by making the control path quiet too.
;
; The guard violation surfaces as "ACL2 Error [Evaluation]", which MUST-FAIL
; treats as a soft error -- hence plain MUST-FAIL and not :expected :hard.
(must-fail (assert-event (equal (apply$ *control* '(-5)) t)))

; For the record: zpf's own logical value at -5, proved rather than evaluated,
; so the assertions above are anchored to the logic and not to each other.
(defthm zpf-of-minus-5-is-t
  (equal (zpf -5) t)
  :hints (("Goal" :in-theory (union-theories '(zpf zp) (theory 'minimal-theory))))
  :rule-classes nil)
