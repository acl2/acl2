; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 68, part 2 of 2: three more unprotected evaluators of user :program
; code.  Part 1 (computed hints, override hints, table) is new-92; the general
; defect and the make-event fix it is a sibling of are documented there.
;
; THE THREE PATHS, each a certified proof of nil:
;
;   :instructions            pc-macroexpand (proof-builder-a.lisp:573)
;                            evaluates a proof-builder macro command with
;                            xtrans-eval at :584.  define-pc-macro expands,
;                            via pc-meta-or-macro-defun (:477-481), into a
;                            defun carrying (xargs :mode :program :stobjs
;                            state), so the body runs in raw Lisp.
;
;   custom keyword hints     custom-keyword-hint-interpreter1
;                            (history-management.lisp:16128) evaluates the
;                            user's GENERATOR with xtrans-eval@par at :16208,
;                            and the value BECOMES the goal's keyword-alist.
;                            (The two checker sites, :16052 and :16180,
;                            discard their value and so cannot leak.)
;
;   default hints            eval-and-translate-hint-expression
;                            (history-management.lisp:17565), xtrans-eval@par
;                            at :17647.  Worth singling out because the
;                            poisoned theorem carries NO :hints at all, and
;                            default hints are world-global, so a
;                            set-default-hints in an INCLUDED book poisons
;                            every later theorem in the including book.
;
; HISTORICAL-FIX GAP, exactly.  pc-command-table-guard
; (proof-builder-a.lisp:398-409) is
;
;    (and (symbolp key) (function-symbolp key wrld)
;         (or (eq val 'macro) (eq val 'atomic-macro) (eq val 'meta)
;             (and (eq val 'primitive) (global-val 'boot-strap-flg wrld))))
;
; and immediately below it, at :418-432, sits a COMMENTED-OUT certifying
; exploit introduced by its own comment: "Before adding this table guard after
; Version_4.3, we were able to certify the following book", using
; define-pc-primitive and :instructions (:foo) to prove nil.  So 'primitive was
; gated on boot-strap-flg and 'meta is gated elsewhere (by the in-verify-flg
; test at proof-builder-b.lisp:124), while 'macro and 'atomic-macro were left
; open -- and they reach nil by the bad-object route below.
;
; POLARITY: RED while present -- every MUST-FAIL below fails.  GREEN once
; xtrans-eval checks its result or binds safe-mode.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

; ---- :instructions (proof-builder macro command) ------------------------
(must-fail
 (progn
   (define-pc-macro n93-badpc ()
     (value (list 'use
                  (list :instance 'char-code-linear
                        (list 'x (list 'quote (code-char 300)))))))
   (defthm n93-badnil-instructions nil
     :instructions (n93-badpc)
     :rule-classes nil)))

; ---- custom keyword hint (the generator) --------------------------------
(defun n93-mk-ckh (kwal)
  (declare (xargs :mode :program) (ignore kwal))
  (list :use (list (list :instance 'char-code-linear
                         (list 'x (list 'quote (code-char 300)))))))

(must-fail
 (progn
   (add-custom-keyword-hint :n93-bad (value (n93-mk-ckh keyword-alist)))
   (defthm n93-badnil-ckh nil
     :hints (("Goal" :n93-bad t))
     :rule-classes nil)))

; ---- default hints ------------------------------------------------------
(defun n93-mk-dh (wrld)
  (declare (xargs :mode :program) (ignore wrld))
  (list :use (list (list :instance 'char-code-linear
                         (list 'x (list 'quote (code-char 300)))))))

; The defthm carries no :hints whatsoever.  The set-default-hints nil at the
; end keeps the poison out of the rest of this book if the progn succeeds.
(must-fail
 (progn (set-default-hints '((n93-mk-dh world)))
        (defthm n93-badnil-dh nil :rule-classes nil)
        (set-default-hints nil)))

; CONTROL 1: proof-builder PRIMITIVES are closed, which is the Version_4.3 fix
; whose siblings this book is about.  define-pc-primitive must be refused
; outside the boot-strap.
(must-fail
 (progn (program)
        (set-state-ok t)
        (define-pc-primitive n93-foo (&rest rest-args)
          (declare (ignore rest-args))
          (mv (change-pc-state pc-state :goals (cdr goals)) state))
        (logic)
        (defthm n93-primitive-bug nil :instructions (:n93-foo)
          :rule-classes nil)))

; CONTROL 2: proof-builder META commands are closed, by the in-verify-flg gate
; at proof-builder-b.lisp:124.
(must-fail
 (progn (define-pc-meta n93-mymeta () (value t))
        (defthm n93-meta-bug (equal (car (cons x y)) x)
          :instructions (n93-mymeta)
          :rule-classes nil)))

; CONTROL 3: an ordinary :logic-mode proof-builder macro must keep working, so
; the fix cannot be to ban define-pc-macro.
(define-pc-macro n93-okpc ()
  (value 'prove))
(defthm n93-control-pc-macro-works
  (equal (car (cons x y)) x)
  :instructions (n93-okpc)
  :rule-classes nil)
