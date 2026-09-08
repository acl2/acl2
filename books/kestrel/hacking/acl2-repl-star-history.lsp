; ACL2 hack: acl2-repl-star-history.lsp
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Author: Eric McCarthy (bendyarm on GitHub)
; Redefines ld-read-command, originally:
; Copyright (C) 2026, Regents of the University of Texas
; This version of ACL2 is a descendant of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; ------------------------------------------------------------------------------
;
; Make the Common Lisp REPL history variables usable at the *normal* ACL2
; top-level loop (no raw mode needed when typing):
;
;   *  **  ***   -> the value(s) returned by the previous, 2nd-previous, and
;                   3rd-previous commands (like CL's *, **, ***)
;   +  ++  +++   -> the (original, as-typed) previous, 2nd-previous, and
;                   3rd-previous input *forms* (like CL's +, ++, +++)
;
; Example:
;   ACL2 !>(parse-from-string "(frame [] 5)")
;   ((EXPR :FRAME NIL ...))
;   ACL2 !>(make-self *)            ; == (make-self '((EXPR :FRAME NIL ...)))
;
; How to set up: add the following form to your ~/acl2-customization.lsp file:
;
;   (ld "kestrel/hacking/acl2-repl-star-history.lsp" :dir :system :ld-missing-input-ok t)
;
; How it works: ACL2's normal loop forbids * etc. as variables (they are
; COMMON-LISP-package symbols; the error is from TRANSLATE, not the reader).
; So we hook the loop's read step (ld-read-command), and *between read and
; translate* walk the just-read form, replacing * ** *** in evaluation
; position with (repl-hist-val n state), and + ++ +++ with the literal,
; quoted previous original form.  Operator position (e.g. (* 2 3)) and
; QUOTE / FUNCTION subforms (e.g. '*) are left untouched.
;
; The hook fires ONLY at the interactive top level (ld-level 1) and ONLY when
; NOT in raw mode (in raw mode * legitimately denotes the CL special variable).
;
; This installs a trust tag and redefines a system function in raw Lisp, so it
; cannot be a certified book -- hence the .lsp extension.  Book certification
; runs with ACL2_CUSTOMIZATION=NONE, so this file never affects certification.
;
; Idempotent: LDing it more than once is safe (the genuine original of
; ld-read-command is captured only once; the input-history stack is preserved).
;
; ---------------------------------------------------------------------------
; Relation to Peter Dillinger's "Hacking & Extending ACL2" toolkit
; (books/hacking/, a.k.a. the ACL2s "hacker" library):
;
;   That toolkit is the sanctioned, principled way to do raw-Lisp system
;   surgery.  In particular books/hacking/raw.lisp provides MODIFY-RAW-DEFUN,
;   which is essentially the clean version of what we do by hand below: it
;   copies the genuine original of a raw function under a new name and then
;   redefines it (with undo-stack bookkeeping, ttag management, etc.).  See
;   also REDEFUN / REDEFUN+REWRITE (override or pattern-patch an existing
;   :program function), the REWRITE-CODE package, and DEFCODE.  A close cousin
;   of THIS file is books/hacking/evalable-ld-printing.lisp, which hooks the
;   OUTPUT side of the loop (ld-print-results) via MODIFY-RAW-DEFUN, gated by a
;   state-global flag -- structurally the mirror image of the read-side hook
;   here.
;
;   We deliberately do NOT use that toolkit here:
;     - A customization file cannot be a certified book anyway (it runs raw
;       Lisp at startup), so the book-oriented benefits (certifiability,
;       undoability, ttag subsumption) buy us little in this setting.
;     - We want this file to be standalone and dependency-free: no
;       INCLUDE-BOOK of the hacking library, no extra load time, nothing to
;       keep in sync.  It is just LD'd from a customization file.
;     - The hand-written wrapper is small and self-documenting; mirroring it
;       onto MODIFY-RAW-DEFUN would mostly hide the one subtlety that matters
;       (the raw-mode / ld-level guard), not remove it.
;   If this were ever packaged as a real book, MODIFY-RAW-DEFUN on
;   ld-read-command would be the idiomatic core.
;
; ---------------------------------------------------------------------------
; Aspirational note: the nicest outcome would be for read-time access to the
; previous result(s)/input(s) to land in core ACL2 itself (so no raw-Lisp hook
; is needed).  Until then, this file is the lightweight stopgap.
;
; ---------------------------------------------------------------------------

(in-package "ACL2")               ; restored by LD on exit; keeps this file self-contained

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Part 1 (normal mode): value accessors + multiple-entry history.

; Return the value the REPL *displayed* for an ld-history entry: the single
; value, or -- for an error triple (mv erp val state), as events produce --
; the val component, or the whole list for other multiple-value returns.
(defun repl-hist-entry-value (entry)
  (declare (xargs :mode :program))
  (let ((stobjs-out (ld-history-entry-stobjs-out entry)))
    (cond ((null stobjs-out) nil)                              ; eval error
          ((null (cdr stobjs-out)) (ld-history-entry-value entry)) ; single value
          ((equal stobjs-out '(nil nil state))                ; error triple
           (cadr (ld-history-entry-value entry)))
          (t (ld-history-entry-value entry)))))               ; other mv

; Value of the command N entries back (0 = previous command), or nil.
(defun repl-hist-val (n state)
  (declare (xargs :mode :program :stobjs state))
  (let ((entry (nth n (ld-history state))))
    (and entry (repl-hist-entry-value entry))))

; Switch to multiple-entry mode so ** and *** have data (no-op if already on).
(adjust-ld-history t state)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Part 2 (raw Lisp, behind a ttag): the read-time rewriter.

(set-raw-mode-on!)

; * ** *** -> value accessor calls (evaluated at eval time against ld-history).
(defparameter *repl-val-map*
  (list (cons '*   '(repl-hist-val 0 state))
        (cons '**  '(repl-hist-val 1 state))
        (cons '*** '(repl-hist-val 2 state))))

; + ++ +++ -> index into *repl-input-history* (inlined as a quoted literal).
(defparameter *repl-input-map*
  (list (cons '+ 0) (cons '++ 1) (cons '+++ 2)))

; Stack of ORIGINAL (pre-rewrite) top-level forms, most recent first.
; defvar (not defparameter) so reloading this file preserves the stack.
(defvar *repl-input-history* nil)

(defun repl-rewrite-stars-list (lst)
  (if (atom lst)                            ; handles nil and improper tails
      lst
      (cons (repl-rewrite-stars (car lst))
            (repl-rewrite-stars-list (cdr lst)))))

(defun repl-rewrite-stars (form)
  (cond ((symbolp form)
         (let ((v (assoc form *repl-val-map* :test #'eq)))
           (cond (v (cdr v))                                   ; * ** ***
                 (t (let ((i (assoc form *repl-input-map* :test #'eq)))
                      (if i                                    ; + ++ +++
                          (list 'quote (nth (cdr i) *repl-input-history*))
                          form))))))
        ((atom form) form)
        ((member (car form) '(quote function) :test #'eq) form) ; don't descend
        (t (cons (if (consp (car form))
                     (repl-rewrite-stars (car form))           ; ((lambda ...) ...)
                     (car form))                               ; operator: leave alone
                 (repl-rewrite-stars-list (cdr form))))))

; Capture the genuine original ONCE (idempotency: never wrap the wrapper).
(unless (fboundp 'ld-read-command-orig)
  (setf (symbol-function 'ld-read-command-orig)
        (symbol-function 'ld-read-command)))

(defun ld-read-command (state)
  (multiple-value-bind (eofp erp keyp form st)
      (funcall (symbol-function 'ld-read-command-orig) state)
    (cond
     ((or eofp erp) (values eofp erp keyp form st))
     ;; only the interactive top level, and never in raw mode
     ((not (and (eql (f-get-global 'ld-level state) 1)
                (not (raw-mode-p state))))
      (values eofp erp keyp form st))
     (t
      (let ((new-form (if keyp form (repl-rewrite-stars form))))
        (push form *repl-input-history*)                       ; original, pre-rewrite
        (when (> (length *repl-input-history*) 200)
          (setf *repl-input-history* (subseq *repl-input-history* 0 100)))
        (values eofp erp keyp new-form st))))))

(set-raw-mode nil)
(defttag nil)
