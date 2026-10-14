; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 60: MV-LIST smuggled into a quoted LAMBDA object.  The logical mv-list
; (axioms.lisp:13859) is (lambda (input-arity x) x); the raw one (:13866) is a
; MACRO expanding to (multiple-value-list x).  For a single-valued x the macro
; CONSES and the logic does not, and the arity argument is ignored outright by
; the macro.
;
; logic-code-to-runnable-code (defuns.lisp:9405-9409) emits the call unchanged
; on the stated premise "Since term is a fully translated term, we know it is of
; the form (mv-list 'k expr) where k is an explicit integer greater than 1".
; make-compileable-guard-and-body-lambdas restates it (:9602-9605): "if x is not
; from a lambda$ it was typed by the user and he or she couldn't have used mv-let
; or loop$ in it anyway because quoted LAMBDA objects are not translated."
;
; But MV-LIST *is* the translation of mv-let, and it is an ordinary :logic-mode,
; guard-verified, badged, tame binary function symbol -- so termp,
; executable-tamep and well-formed-lambda-objectp all accept it.
;
; Measured, one session:
;   (apply$ '(lambda (y) (mv-list 'nil y)) '(7))   => (7)
;   (ev$ '(mv-list 'nil y) '((y . 7)))             => 7
;   (apply$ 'mv-list '(nil 7))                     => 7
;   (well-formed-lambda-objectp '(lambda (y) (mv-list 'nil y)) (w state)) => T
; Three routes, one ground term, two values -- and only the compiled
; quoted-lambda route is wrong, which isolates the defect to
; logic-code-to-runnable-code rather than to mv-list.
;
; THE CLASS, ENUMERATED: the ACL2 function symbols that are macros or special
; operators in raw Lisp are exactly DECREMENT-BIG-N, MV-LIST, RETURN-LAST,
; TO-DF, WORMHOLE-EVAL and ZP-BIG-N.  RETURN-LAST is Finding 56; MV-LIST is this
; one; TO-DF was measured safe (ec-call-wrapped); the other three have no badge
; so cannot appear in a lambda BODY, but are reachable in a lambda GUARD (N233).
;
; No warrant and no prog2$ are needed, because mv-list is a primitive.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun g (x)
  (declare (xargs :guard t))
  (apply$ '(lambda (y) (mv-list 'nil y)) (list x)))

; The logical value, proved first and honestly: inside the prover *aokp* is nil,
; so apply$-lambda falls through to apply$-lambda-logical.  Must stay provable.
(defthm g-logic (equal (g 7) 7) :rule-classes nil)

(memoize 'g)

; THE DEFECT, in two steps.  At the TOP LEVEL *aokp* is t, so the cl-cache
; compiles the body, raw MV-LIST conses, and the memo table is populated with
; the wrong value.  The ASSERT-EVENT is what forces that evaluation -- without
; it the table stays empty and the prover never sees the raw value, so the
; assert-event is load-bearing and not decoration.
(must-fail (assert-event (equal (g 7) '(7))))

; And then the prover reads the memo entry.  (Both MUST-FAILs are the defect:
; after a fix the assert-event fails because (g 7) is 7, and this theorem is
; unprovable.  Either one firing is the red state.)
(must-fail (defthm g-raw (equal (g 7) '(7)) :rule-classes nil))

; CONTROL 1: translate must keep refusing mv-list in a defun body, both with a
; non-integer and with an integer arity, so the hole is the quoted-LAMBDA path.
(must-fail (defun r1 (x) (declare (xargs :guard t)) (mv-list 'nil x)))
(must-fail (defun r2 (x) (declare (xargs :guard t)) (mv-list '2 x)))

; CONTROL 2: a LEGITIMATE mv-list on a genuine mv call in a guard-verified
; compiled defun must keep working -- raw and logic must agree -- so the fix
; cannot be to ban mv-list.
(defun two (x) (declare (xargs :guard (integerp x))) (mv x (+ x 1)))
(defun k (x) (declare (xargs :guard (integerp x))) (mv-list 2 (two x)))
(defthm k-logic (equal (k 5) '(5 6)) :rule-classes nil)
