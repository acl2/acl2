; Copyright (C) 2020, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")
(f-put-global 'trace-co (@ standard-co) state)
(include-book "projects/apply/top" :dir :system)

; This file tests apply$'s support for :program mode functions.  The goal is to
; allow such functions to evaluate in the evaluation theory without allowing
; them to enter into proofs.  Part of the implementation required allowing
; :program mode functions to be badged by the new (V8.4) facility defbadge.
; Prior to that, defwarrant issued both badges and warrants.  That meant that
; having a badge implied having (or not needing) a warrant.  Now :program mode
; functions can have badges but will never have warrants.  So some of these
; tests are aimed at confirming that the prover doesn't confuse having a badge
; with having a warrant.  Other tests experiment with :logic mode functions
; using lambda expressions that use :program mode functions.  This can't be
; prevented (though translate makes an effort).  So ultimately it must be
; dealt-with at proof and evaluation time.

; We will introduce a function named HELLO and explore the behavior of
; apply$ in several contexts.



; General Guideline:

; APPLY$, EV$, LAMBDA$, and LOOP$ should all behave analogously
; with respect to translation, evaluation in the evaluation theory,
; evaluation within the prover, and use in defuns.

; Caveat: Don't take this too literally!  Defun must enforce more rules than
; prove simply to support raw Lisp evaluation of guard verified functions.  The
; evaluation theory can handle :PROGRAM mode functions but the logic cannot.

; Our Tests:

(defconst *tests*
  '((trace$ hello)
    (apply$ 'hello '(john))
    (ev$ '(hello e) '((e . john)))
    (apply$ (lambda$ (e) (hello e)) '(john))
    (apply$ `(lambda (e) (hello e)) '(john))
    (apply$ (lambda$ () (hello 'john)) nil)
    (loop$ for e in '(john mary) collect (hello e))
    (loop$ for e in '("John" "Mary") collect (hello e))
    (set-guard-checking nil)
    (loop$ for e in '("John" "Mary") collect (hello e))
    (set-guard-checking t)
    (defun caller1 (e)
      (declare (xargs :guard t :verify-guards nil))
      (apply$ 'hello (list e)))
    (verify-guards caller1)
    (trace$ caller1)
    (caller1 'john)
    (caller1 "Mary and Tom")
    (set-guard-checking nil)
    (caller1 "Mary and Tom")
    (set-guard-checking t)
    (defun caller2 (e)
      (declare (xargs :guard (symbolp e) :verify-guards nil))
      (apply$ (lambda$ (d) (declare (xargs :guard (symbolp d)))
                       (hello d))
              (list e)))
    (verify-guards caller2)
    (trace$ caller2)
    (caller2 'john)
    (caller2 "Mary and Tom")
    (set-guard-checking nil)
    (caller2 "Mary and Tom")
    (set-guard-checking t)
    (thm (equal (apply$ 'hello '(john)) '(hi john)))
    (thm (equal (apply$ (lambda$ () (hello 'john)) nil) '(hi john)))
    (thm (equal (apply$ `(lambda () (hello 'john)) nil) '(hi john)))
    (thm (equal (apply$ (lambda$ () (hello 'john)) nil) '(hi john))
         :hints (("Goal" :in-theory (disable beta-reduction))))
    (thm (implies (warrant hello) (equal (apply$ 'hello '(john)) '(hi john))))
    (thm (equal (caller1 'john) '(hi john)))
    (thm (equal (caller2 'john) '(hi john)))
    (defun caller3 (e)
      (declare (xargs :guard t :verify-guards nil))
      (apply$ (car (cons 'hello nil)) (list e)))
    (verify-guards caller3)
    (caller3 'john)
    (caller3 "Mary and Tom")
    (set-guard-checking nil)
    (caller3 "Mary and Tom")
    (set-guard-checking t)
    (thm (equal (caller3 'john) '(hi john)))))

(defconst *sections*
  '((0 "HELLO is an undefined symbol")
    (1 "HELLO is an unbadged :program mode function")
    (2 "HELLO is a badged :program mode function")
    (3 "HELLO is a badged but unwarranted :logic mode function")
    (4 "HELLO is a badged and warranted :logic mode function.")
    (5 "HELLO is a badged and warranted, guard-verified :logic mode function")))

(defmacro section (n)
  `(pprogn (fms "~%-----------------------------------------------------------------~%~
               ~x0. ~@1~%"
               (list (cons #\0 ,n)
                     (cons #\1 (cdr (assoc ,n *sections*))))
               (@ standard-co)
               state nil)
           (value :invisible)))

(section 0)
; -----------------------------------------------------------------
; 0.  HELLO is an undefined symbol

(deflabel eventually-undo-back-to-here)
(defbadge hello)
(ld *tests* :ld-error-action :continue :ld-pre-eval-print t)
(ubt! 'eventually-undo-back-to-here)

(section 1)
; -----------------------------------------------------------------
; 1.  HELLO is an unbadged :program mode function

(defun hello (x)
  (declare (xargs :mode :program
                  :guard (symbolp x)
                  :verify-guards nil))
  (list 'HI x))

(deflabel eventually-undo-back-to-here)
(ld *tests* :ld-error-action :continue :ld-pre-eval-print t)
(ubt! 'eventually-undo-back-to-here)

(section 2)
; -----------------------------------------------------------------
; 2.  HELLO is a badged :program mode function

(defbadge hello)
(deflabel eventually-undo-back-to-here)
(ld *tests* :ld-error-action :continue :ld-pre-eval-print t)
(ubt! 'eventually-undo-back-to-here)

(section 3)
; -----------------------------------------------------------------
; 3.  HELLO is a badged but unwarranted :logic mode function

(verify-termination hello)
(deflabel eventually-undo-back-to-here)
(ld *tests* :ld-error-action :continue :ld-pre-eval-print t)
(ubt 'eventually-undo-back-to-here)

(section 4)
; -----------------------------------------------------------------
; 4.  HELLO is a badged and warranted :logic mode function.
(defwarrant hello)
(deflabel eventually-undo-back-to-here)
(ld *tests* :ld-error-action :continue :ld-pre-eval-print t)
(ubt 'eventually-undo-back-to-here)

(section 5)
; -----------------------------------------------------------------
; 5.  HELLO is a badged and warranted, guard-verified :logic mode function
(verify-guards hello)
(deflabel eventually-undo-back-to-here)
(ld *tests* :ld-error-action :continue :ld-pre-eval-print t)
(ubt 'eventually-undo-back-to-here)
; -----------------------------------------------------------------

; =================================================================
; Part II  Testing the Prover

; The aim of these tests is primarily to check that the prover does not expand
; :program mode functions.  This test suite was developed separately from the
; one above and so there is a lot of redundancy between the two suites.  In
; this suite, instead of using HELLO consistently and changing its attributes
; with various events like defbadge, verify-termination, etc., I introduce
; differently named functions whose names suggest their attributes.

; Some problems are caught by translate but others are allowed into the prover
; and caught there.  The best example of this is the first two forms below.
; Lambda$ requires its body be translateable.  But we can always just cons up a
; lambda object and force the prover to deal with it.  We disable
; beta-reduction to give rewrite-lambda-object a chance to rewrite the
; (illegal) body.

; This is a translate error:
(thm (equal (apply$ (lambda$ nil (undefined 'john)) nil)
            (apply$ 'UNDEFINED '(john))))

; Beta-reduction exposes the undefined expression to ev$ but that
; fails.
(thm (equal (apply$ `(lambda nil (undefined 'john)) nil)
            (apply$ 'UNDEFINED '(john))))

; Disabling beta-reduction preserves the lambda expression and thus exposes it
; to rewrite-lambda-object, which rejects the attempt to rewrite it (with a
; sensible warning if such warnings are enabled).

(thm (equal (apply$ `(lambda nil (undefined 'john)) nil)
            (apply$ 'UNDEFINED '(john)))
     :hints (("Goal" :in-theory (disable beta-reduction))))

(defun program-mode-with-no-badge (x)
  (declare (xargs :mode :program))
  (list 'hi x))

; Translate error:
(thm (equal (apply$ (lambda$ nil (program-mode-with-no-badge 'john)) nil)
            '(HI JOHN)))


; Beta-reduction eliminates lambda but then fails in ev$
(thm (equal (apply$ `(lambda nil (program-mode-with-no-badge 'john)) nil)
            '(HI JOHN)))

; Rewrite-lambda-object gets the lambda but rejects (with warning) rewriting
; it.
(thm (equal (apply$ `(lambda nil (program-mode-with-no-badge 'john)) nil)
            '(HI JOHN))
     :hints (("Goal" :in-theory (disable beta-reduction))))

(defun program-mode-with-badge-but-no-warrant (x)
  (declare (xargs :mode :program))
  (list 'hi x))

(defbadge program-mode-with-badge-but-no-warrant)

; Once upon a time, rewrite-lambda-object barged into a :program mode term.
; But no longer...  The optional warning message from rewrite-lambda-object
; announces that we didn't rewrite the lambda object because it contains a
; :program mode function.

; Beta-reduction eliminates the lambda and we fail in ev$.  The ev$ is actually
; a ground term but we don't evaluate it, dodging another possible bug!

(thm (equal (apply$ (lambda$ nil (program-mode-with-badge-but-no-warrant 'john)) nil)
            '(HI JOHN)))

; The checkpoint is:
; (EQUAL (HIDE (EV$ '(PROGRAM-MODE-WITH-BADGE-BUT-NO-WARRANT 'JOHN)
;                   NIL))
;        '(HI JOHN))
; and there is no explanation of why EV$ didn't just run or open up.
; We can make it expand:

(thm (equal (apply$ (lambda$ nil (program-mode-with-badge-but-no-warrant 'john)) nil)
            '(HI JOHN))
     :hints (("Goal" :in-theory (enable ev$ (:executable-counterpart ev$)))))

; but that just introduces a case split on (badge
; 'program-mode-with-badge-but-no-warrant).  Of course, the symbol has a badge
; but that fact isn't available to the logic.  The failure here might be
; mysterious to the user!  Nothing about the proof attempt highlights the fact
; that we're dealing with a program mode function!

; Disabling beta-reduction allows rewrite-lambda-object to get the lambda, but
; it rejects rewriting it.
(thm (equal (apply$ (lambda$ nil (program-mode-with-badge-but-no-warrant 'john)) nil)
            '(HI JOHN))
     :hints (("Goal" :in-theory (disable beta-reduction))))

; But before we get too bent out of shape about that, let's forget about
; :program mode functions and see how we handle the same situation for :logic
; mode functions.

(defun logic-mode-with-badge-but-no-warrant (x)
  (declare (xargs :mode :logic
                  :guard (symbolp x)
                  :verify-guards nil))
  (list 'HI x))

(defbadge logic-mode-with-badge-but-no-warrant)

; If we let rewrite-lambda-object have a shot at this, its warning points out
; that the symbol is unwarranted, analogous to what happened before with
; the symbol being in :program mode.

(thm (equal (apply$ (lambda$ nil (logic-mode-with-badge-but-no-warrant 'john)) nil)
            '(HI JOHN))
     :hints
     (("Goal" :in-theory (disable beta-reduction))))

; And if we let beta-reduction occur and EV$ do its thing

(thm (equal (apply$ (lambda$ nil (logic-mode-with-badge-but-no-warrant 'john)) nil)
            '(HI JOHN)))

; we get a ``mysterious'' checkpoint like before:
; (EQUAL (HIDE (EV$ '(LOGIC-MODE-WITH-BADGE-BUT-NO-WARRANT 'JOHN)
;                   NIL))
;        '(HI JOHN))
; and if we make ev$ expand

(thm (equal (apply$ (lambda$ nil (logic-mode-with-badge-but-no-warrant 'john)) nil)
            '(HI JOHN))
     :hints (("Goal" :in-theory (enable ev$ (:executable-counterpart ev$)))))

; we get the same case split on whether the symbol has a badge.  So while the
; failure of the proof might be mysterious, it's not really a :program mode
; anomaly.  It happens with badged :logic mode functions too.  The only reason
; we never saw it is that before we allowed :program mode functions to be
; badged the only way a function could acquire a badge was to also acquire a
; warrant.  If the user finally twigs to the fact that the symbols in questions
; don't have warrants he or she will use defwarrant and, in the case of the
; :program mode symbol, discover that it's in :program mode.

(defwarrant program-mode-with-badge-but-no-warrant)

(defun logic-mode-with-badge-and-warrant (x)
  (declare (xargs :mode :logic
                  :guard (symbolp x)
                  :verify-guards nil))
  (list 'HI x))

(defbadge logic-mode-with-badge-and-warrant)

(defwarrant logic-mode-with-badge-and-warrant)

; No warrant hyp, so it fails but forces the warrant.
(thm (equal (apply$ (lambda$ nil (logic-mode-with-badge-and-warrant 'john)) nil)
            '(HI JOHN)))

; Succeeds
(thm (implies (warrant logic-mode-with-badge-and-warrant)
              (equal (apply$ (lambda$ nil (logic-mode-with-badge-and-warrant 'john)) nil)
                     '(HI JOHN))))

; If we deny the warrant and allow beta-reduction,
(thm (implies (not (warrant logic-mode-with-badge-and-warrant))
              (equal (apply$ (lambda$ nil (logic-mode-with-badge-and-warrant 'john)) nil)
                     '(HI JOHN))))
; we get an understandable checkpoint:

; (IMPLIES
;  (NOT (APPLY$-WARRANT-LOGIC-MODE-WITH-BADGE-AND-WARRANT))
;  (EQUAL
;   (HIDE
;    (COMMENT
;     "Call failed because the warrant for LOGIC-MODE-WITH-BADGE-AND-WARRANT is not known to be true"
;     (EV$ '(LOGIC-MODE-WITH-BADGE-AND-WARRANT 'JOHN)
;          NIL)))
;   '(HI JOHN)))

; But if we allow rewrite-lambda-object to mess with that lambda$, by disabling
; beta-reduction so that the lambda survives, it actually opens up
; (logic-mode-with-badge-and-warrant 'john) but then rejects the expansion with
; a sensible warning message.

(thm (implies (not (warrant logic-mode-with-badge-and-warrant))
              (equal (apply$ (lambda$ nil (logic-mode-with-badge-and-warrant 'john)) nil)
                     '(HI JOHN)))
     :hints
     (("Goal" :in-theory (disable beta-reduction))))

; Another way, perhaps, to trick the prover into manipulating a :program mode
; function is to define a :logic mode function that calls a :program mode
; function, to verify the guards on the function, and then have a ground
; instance of it occur in a theorem.  We try that now...

; This fails because the body of the loop$ is has not yet been guard
; verified.

(defun run-this-version-1 (x)
  (declare (xargs :mode :logic
                  :guard (symbolp x)))
  (loop$ for e in (list x)
         collect
         :guard (symbolp e)
         (program-mode-with-badge-but-no-warrant e)))

; So we can admit it without verifying guards...  BTW: We do get a warning
; that this logic mode fn uses a program mode function in a :fn slot.

(defun run-this-version-1 (x)
  (declare (xargs :mode :logic
                  :guard (symbolp x)
                  :verify-guards nil))
  (loop$ for e in (list x)
         collect
         :guard (symbolp e)
         (program-mode-with-badge-but-no-warrant e)))

; Then we try to verify the guards of the body:

(verify-guards program-mode-with-badge-but-no-warrant)

; But that fails, explaining that the symbol is in :program mode.

; Of course, we could verify its termination and then verify-guards, but I
; don't want to do that because then the name
; ``program-mode-with-badge-but-no-warrant'' wouldn't make sense because it's
; in :logic mode!  So, in the spirit of that, we do this:

(defun run-this-version-2 (x)
  (declare (xargs :mode :logic
                  :guard (symbolp x)
                  :verify-guards nil))
  (loop$ for e in (list x)
         collect
         :guard (symbolp e)
         (logic-mode-with-badge-but-no-warrant e)))

(verify-guards logic-mode-with-badge-but-no-warrant)

(verify-guards run-this-version-2)

; But of course now it's just a perfect :logic mode, guard verified function
; and there is nothing unusual about it.

; However, it does give us the opportunity to run a function that doesn't
; have a warrant...

(thm (equal (run-this-version-2 'john) '((HI JOHN))))

; But that fails with the same kind of mysterious stoppage we've seen before.

; Finally, let's follow this scheme but use a subfunction with a warrant:

(defun run-this-version-3 (x)
  (declare (xargs :mode :logic
                  :guard (symbolp x)
                  :verify-guards nil))
  (loop$ for e in (list x)
         collect
         :guard (symbolp e)
         (logic-mode-with-badge-and-warrant e)))

(verify-guards logic-mode-with-badge-and-warrant)

(verify-guards run-this-version-3)

; Since logic-mode-with-badge-and-warrant actually has a warrant, we can force it
; and get a helpful checkpoint:

(thm (equal (run-this-version-3 'john)
            '((HI JOHN))))

; But if we disable (:executable-counterpart force) we just get a comment on
; failure to expand:

(thm (equal (run-this-version-3 'john)
            '((HI JOHN)))
     :hints (("Goal" :in-theory (disable (force) run-this-version-3))))
