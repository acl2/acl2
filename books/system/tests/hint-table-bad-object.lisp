; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 68, part 1 of 2: the bad-Lisp-object leak on the hint and table
; paths.  Part 2 is new-93.
;
; THE GENERAL DEFECT.  A :program-mode function is executed by raw Lisp, so it
; can return objects that are not ACL2 objects -- canonically (code-char 300),
; a character whose char-code is 300, contradicting the axiom
; char-code-linear, (< (char-code x) 256).  ACL2's defence is the raw-Lisp
; predicate bad-lisp-objectp (axioms.lisp:23333, chk-bad-lisp-object at
; :23374) plus, on some paths, binding safe-mode to t so code-char's guard is
; enforced.
;
; THE FIX THAT WAS MADE.  make-event's check at other-events.lisp:34720 is now
; UNCONDITIONAL.  Its comment at :34714-34718 reads: "At one time we only did
; the following check when the known-package-alist has changed. ... But we now
; do the check unconditionally, and a very simple example explains why; see
; community book system/tests/make-event-bad-char.lisp."  That book is in the
; tree and says it "illustrates a soundness bug fixed before ACL2
; Version 8.8".
;
; THE SIBLINGS THAT WERE NOT FIXED, each a certified proof of nil:
;   computed hints   xtrans-eval, history-management.lisp:4400, called from
;                    eval-and-translate-hint-expression :17565 at :17647.
;                    xtrans-eval's own comment, :4433: "Note that we do not
;                    evaluate in safe-mode.  Perhaps we should."
;   override hints   apply-override-hint1, history-management.lisp:17406,
;                    xtrans-eval@par at :17419.
;   table            table-fn, history-management.lisp:19280, computing key and
;                    val with simple-translate-and-eval at :19361 and :19372
;                    and passing them to table-fn1 (:19035) unchecked.
;                    simple-translate-and-eval's own comment
;                    (translate.lisp:28260): "we call translate with
;                    logic-modep nil.  Thus, :program mode functions may appear
;                    in x."
;
; The table path is the worst of the three: for an ordinary (non
; acl2-defaults-table) table the event is re-run at include-book, so the bad
; object is installed in every including session's world, not just the
; certifying one.
;
; POLARITY: RED while present -- every MUST-FAIL below fails.  GREEN once
; xtrans-eval and table-fn check their results (or bind safe-mode).

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun n92-pc ()
  (declare (xargs :mode :program))
  (code-char 300))

; ---- computed hint ------------------------------------------------------
(defun n92-mk-hint ()
  (declare (xargs :mode :program))
  (list :use (list (list :instance 'char-code-linear
                         (list 'x (list 'quote (n92-pc)))))))

(must-fail
 (defthm n92-badnil-hint nil :hints ((n92-mk-hint)) :rule-classes nil))

; ---- override hint ------------------------------------------------------
(defun n92-mk-oh (kwal)
  (declare (xargs :mode :program))
  (append (list :use (list (list :instance 'char-code-linear
                                 (list 'x (list 'quote (n92-pc))))))
          kwal))

(must-fail
 (progn (add-override-hints '((n92-mk-oh keyword-alist)))
        (defthm n92-badnil-oh nil
          :hints (("Goal" :in-theory (enable)))
          :rule-classes nil)
        (set-override-hints nil)))

; ---- table --------------------------------------------------------------
(defun n92-read-hint (wrld)
  (declare (xargs :mode :program))
  (list :use
        (list (list :instance 'char-code-linear
                    (list 'x (list 'quote
                                   (cdr (assoc-eq 'k (table-alist 'n92bt
                                                                  wrld)))))))))

(must-fail
 (progn (table n92bt 'k (n92-pc))
        (defthm n92-badnil-table nil
          :hints ((n92-read-hint world))
          :rule-classes nil)))

; CONTROL 1: make-event IS protected -- the same :program-mode value in a
; make-event expansion is refused.  This is the sibling fix, in the same book.
(must-fail
 (make-event (value `(defconst *n92-c* ',(list (n92-pc))))))

; CONTROL 2: defconst is protected by its safe-mode binding
; (other-events.lisp:184-186), so this is refused with a CODE-CHAR guard
; violation rather than accepted.
(must-fail (defconst *n92-d* (n92-pc)))

; CONTROL 3: a LEGAL character through the same computed-hint machinery must
; not prove nil, so the defect is the object and not the hint path.
(defun n92-mk-hint-ok ()
  (declare (xargs :mode :program))
  (list :use (list (list :instance 'char-code-linear
                         (list 'x (list 'quote (code-char 97)))))))
(must-fail
 (defthm n92-control-legal nil :hints ((n92-mk-hint-ok)) :rule-classes nil))

; CONTROL 4: :logic-mode hint generators must keep working, so the fix cannot
; be to ban computed hints.
(defun n92-mk-hint-logic (wrld) (declare (ignore wrld)) '(:in-theory (enable)))
(defthm n92-control-logic-hint
  (equal (car (cons x y)) x)
  :hints ((n92-mk-hint-logic world))
  :rule-classes nil)
