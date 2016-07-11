; ACL2 Sidekick
; Copyright (C) 2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "SIDEKICK")
(include-book "io")
(include-book "std/strings/pretty-program" :dir :system)
(include-book "webcommand")
(set-state-ok t)

(defmacro explore ()
  (push-webcommand (list (cons :action :explore))))

(define sk-explore-th (state)
  :returns (mv json-info state)
  :mode :program
  (b* ((acl2::state-stack (acl2::state-stack))
       ((unless acl2::state-stack)
        (mv (sk-json-error "Not currently verifying a formula.")
            state))

       ;; BOZO seems like we also need to do something with abbreviations, see
       ;; P-BODY in proof-builder-b.lisp
       (hyps         (acl2::hyps t))
       (conc         (acl2::conc t))
       (current-addr (acl2::current-addr t))
       (current-term (acl2::fetch-term conc current-addr))

       (config (str::make-printconfig :home-package
                                      (pkg-witness (current-package state))))

       (ans (list (cons :hyps         (str::pretty-list hyps :config config))
                  (cons :conclusion   (str::pretty conc :config config))
                  (cons :current-addr (str::pretty current-addr :config config))
                  (cons :current-term (str::pretty current-term :config config)))))
    (mv (bridge::json-encode (list (cons :error nil)
                                   (cons :val ans)))
        state)))


(define sk-jsonify-indexed-instrs (indexed-instrs config)
  :mode :program
  (if (atom indexed-instrs)
      nil
    (cons (list (cons :index (caar indexed-instrs))
                (cons :command (str::pretty (cdar indexed-instrs) :config config)))
          (sk-jsonify-indexed-instrs (cdr indexed-instrs) config))))

(define sk-explore-commands (state)
  :returns (mv json-info state)
  :mode :program
  (b* ((state-stack (acl2::state-stack))
       ((unless state-stack)
        (mv (sk-json-error "Not currently verifying a formula.")
            state))
       (config (str::make-printconfig :home-package
                                      (pkg-witness (current-package state))))
       (instrs (acl2::raw-indexed-instrs 1 (length state-stack) state-stack))
       (ans (sk-jsonify-indexed-instrs instrs config)))
    (mv (bridge::json-encode (list (cons :error nil)
                                   (cons :val ans)))
        state)))


(define sk-explore-undo ((num maybe-stringp) state)
  :returns (mv json-info state)
  :mode :program
  (b* ((n (and num (str::strval num)))
       ((unless n)
        (mv (sk-json-error "Error in sk-explore-undo: not a number: ~a" num)
            state))
       ((mv erp ?val state) (acl2-pc::undo (list n) state))
       ((when erp)
        (mv (sk-json-error "acl2-pc::undo returned an error: erp ~a, val ~a"
                           (str::pretty erp) (str::pretty val))
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))

; So how does contrapose work?
; (define-pc-primitive contrapose (&optional n) ...)
;   defines acl2-pc::contrapose which returns (mv pc-state state)
;   where (pc-value state-stack) has not yet been changed for state
; it seems like the idea is to use pc-single-step-primitive instead?

;; (trace$ (acl2::pc-single-step-primitive
;;          :entry (list :instr (first acl2::arglist))
;;          :exit (list :er (first acl2::values)
;;                      :val (second acl2::values))))

; (verify)
; (contrapose 4)
; 1> (:INSTR (ACL2-PC::CONTRAPOSE 4))
; *** NO CHANGE *** -- There are no top-level hypotheses.
; <1 (:ER NIL :VAL NIL)

(define sk-explore-contrapose ((num maybe-stringp) state)
  :returns (mv json-info state)
  :mode :program
  (b* ((n (and num (str::strval num)))
       (- (cw "Sidekick: contrapose ~x0.~%" n))
       ((unless n)
        (mv (sk-json-error "Error in sk-explore-contrapose: not a number: ~a" num)
            state))
       ((mv erp ?val state) (acl2::pc-single-step-primitive (list 'acl2-pc::contrapose n) state))
       ((when erp)
        (mv (sk-json-error "acl2-pc::contrapose returned an error: erp ~a, val ~a"
                           (str::pretty erp) (str::pretty val))
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))

(define sk-explore-demote ((num maybe-stringp) state)
  :returns (mv json-info state)
  :mode :program
  (b* ((n (and num (str::strval num)))
       (- (cw "Sidekick: demote ~x0.~%" n))
       ((unless (or (not num)
                    (equal num "")
                    n))
        (mv (sk-json-error "Error in sk-explore-demote: bad argument: ~a" num)
            state))
       (instr (if (natp n)
                  (list 'acl2-pc::demote n)
                (list 'acl2-pc::demote)))
       ((mv erp ?val state) (acl2::pc-single-step-primitive instr state))
       ((when erp)
        (mv (sk-json-error "acl2-pc::demote returned an error: erp ~a, val ~a"
                           (str::pretty erp) (str::pretty val))
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))

(define sk-explore-drop ((num maybe-stringp) state)
  :returns (mv json-info state)
  :mode :program
  (b* ((n (and num (str::strval num)))
       (- (cw "Sidekick: drop ~x0.~%" n))
       ((unless n)
        (mv (sk-json-error "Error in sk-explore-drop: not a number: ~a" num)
            state))
       ((mv erp ?val state) (acl2::pc-single-step-primitive (list 'acl2-pc::drop n) state))
       ((when erp)
        (mv (sk-json-error "acl2-pc::drop returned an error: erp ~a, val ~a"
                           (str::pretty erp) (str::pretty val))
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))

(define sk-explore-split (state)
  :returns (mv json-info state)
  :mode :program
  (b* (((mv erp ?val state) (acl2::pc-single-step '(acl2-pc::split) state))
       ((when erp)
        (mv (sk-json-error "acl2-pc::split returned an error: erp ~a, val ~a"
                           (str::pretty erp) (str::pretty val))
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))

(define sk-explore-pro (state)
  :returns (mv json-info state)
  :mode :program
  (b* (((mv erp ?val state) (acl2::pc-single-step '(acl2-pc::pro) state))
       ((when erp)
        (mv (sk-json-error "acl2-pc::pro returned an error: erp ~a, val ~a"
                           (str::pretty erp) (str::pretty val))
            state))
       (ans (bridge::json-encode (list (cons :error nil)))))
    (mv ans state)))



#||

(sk-explore-th state) ;; Good, error.
(verify (equal (append x y) (append y x)))
exit
(sk-explore-th state)
;; cool, seems to work

||#



;; (define-pc-macro th (&optional hyps-indices govs-indices)
;;   (declare (ignore hyps-indices govs-indices))

;;   (when-goals-trip
;;    (value `(do-all-no-prompt (hyps ,@args)
;;                              (lisp (io? proof-builder nil state
;;                                         nil
;;                                         (fms0 "~%The current subterm is:~%")))
;;                              p))))



;; (defmacro define-pc-macro (raw-name formals &rest body)
;;   (define-pc-meta-or-macro-fn 'macro raw-name formals body))

;; (defun define-pc-meta-or-macro-fn (command-type raw-name formals body)
;;   (let ((name (make-official-pc-command raw-name)) )
;;     (mv-let
;;      (doc body)
;;      (remove-doc
;;       (case command-type
;;             (meta "  (meta)")
;;             (macro "  (macro)")
;;             (atomic-macro "  (atomic macro)")
;;             (otherwise ""))
;;       body)
;;      `(install-new-pc-meta-or-macro ,command-type ,raw-name ,name
;;                                     ,formals ,doc ,body))))

;; (defmacro install-new-pc-meta-or-macro (command-type raw-name name formals doc body)
;;   `(progn ,(pc-meta-or-macro-defun raw-name name formals doc body)
;;           (add-pc-command ,name ',command-type)))

;; (defun pc-meta-or-macro-defun (raw-name name formals doc body)
;;   `(defun ,name (args state)
;;      ;; notice that args aren't ignored, since even if they're nil, they're
;;      ;; used for arity checking
;;      (declare (xargs :mode :program :stobjs state))
;;      ,@(and doc (list doc))
;;      (er-progn
;;       (check-formals-length ',formals args ',raw-name ',name state)
;;       (let ((state-stack (state-stack))
;;             ,@(make-let-pairs-from-formals formals 'args))
;;         ;; in case we have a doc-string and/or declare forms
;;         ,@(butlast body 1)
;;         (let ((very-silly-copy-of-state-stack state-stack))


;; (defmacro verify (&optional (raw-term 'nil raw-term-supplied-p)
;;                             &key
;;                             event-name
;;                             (rule-classes '(:rewrite))
;;                             instructions)
;;   (if (and raw-term-supplied-p (eq raw-term nil))
;;       '(pprogn
;;         (io? proof-builder nil state
;;              nil
;;              (fms0 "It is not permitted to enter the interactive proof-builder ~
;;                     with a goal of NIL!  If you really MEANT to do such a ~
;;                     thing, (VERIFY 'NIL).~%"))
;;                (value :invisible))
;;     `(verify-fn ',raw-term ',raw-term-supplied-p ',event-name
;;                 ',rule-classes ',instructions state)))


;; (defun pc-main (term raw-term event-name rule-classes instr-list
;;                      quit-conditions pc-print-prompt-and-instr-flg state)
;;   (pprogn (install-initial-state-stack term raw-term event-name rule-classes)
;;           (pc-main1 instr-list quit-conditions pc-print-prompt-and-instr-flg
;;                     state)))

;; (defun pc-main1 (instr-list quit-conditions pc-print-prompt-and-instr-flg
;;                             state)
;;   (with-prover-step-limit!
;;    :start
;;    (pc-main-loop instr-list quit-conditions t pc-print-prompt-and-instr-flg
;;                  state)))


;; (defun pc-main-loop (instr-list
;;                      quit-conditions
;; ; Quit-conditions indicates when we want to quit; it is a list of atoms.
;; ; 'signal means that we quit when there's a signal, while 'value means that we
;; ; quit when the value is nil.  If quit-conditions is empty (nil) then we keep
;; ; going, no matter what.  However, a signal to quit (i.e. *pc-complete-signal*)
;; ; is always obeyed if 'exit is a quit-condition.
;;                      last-value
;;                      pc-print-prompt-and-instr-flg
;;                      state)

;; ; Returns an error triple whose state has the new state-stack "installed".
;; ; Here instr-list is a (true) list of instructions or else is a non-NIL atom,
;; ; probably *standard-oi*, from which the instructions are to be read.  Notice
;; ; that by taking (append instrs <stream>), one is able to get the system to
;; ; read from the instr-list input until there are no more instructions, and then
;; ; to read from the stream.

;; ; This only returns non-nil if we exit successfully, or if all instructions
;; ; succeed (null erp, non-nil value) without error.

;;   (if (null instr-list)
;;       (mv nil last-value state)
;;     (mv-let
;;      (col state)
;;      (if pc-print-prompt-and-instr-flg
;;          (print-pc-prompt state)
;;        (mv 0 state))
;;      (mv-let
;;       (erp instr state)
;;       (if (consp instr-list)
;;           (pprogn (if pc-print-prompt-and-instr-flg
;;                       (io? proof-builder nil state
;;                            (col instr-list)
;;                            (fms0 "~y0~|"
;;                                  (list (cons #\0
;;                                              (car instr-list)))
;;                                  col))
;;                     state)
;;                   (value (car instr-list)))
;;         (state-global-let*
;;          ((infixp nil))
;;          (catch-throw-to-local-top-level
;;           (read-object instr-list state))))
;;       (cond
;;        (erp ; read error
;;         (pprogn
;;          (io? proof-builder nil state nil
;;               (fms0
;;                "~|~%~
;;                 /----------------------------------------------------\\~%~
;;                 |        NOTE: Read error -- input discarded.        |~%~
;;                 | Submit EXIT if you want to exit the proof-builder. |~%~
;;                 \\----------------------------------------------------/~%"))
;;          (pc-main-loop instr-list quit-conditions last-value
;;                        pc-print-prompt-and-instr-flg state)))
;;        (t (mv-let
;;            (signal val state)
;;            (catch-throw-to-local-top-level
;;             (pc-single-step
;;              (make-official-pc-instr instr)
;;              state))
;;            (cond
;;             ((and signal
;;                   (or (member-eq 'signal quit-conditions)
;;                       (and (eq signal *pc-complete-signal*)
;;                            (member-eq 'exit quit-conditions))))
;;              (mv signal val state))
;;             ((and (null val) (member-eq 'value quit-conditions))
;;              (mv signal val state))
;;             (t (let ((new-last-value

;; ; We ultimately "succeed" if and only if every instruction "succeeds".  We use
;; ; a let-binding here in order to avoid an Allegro CL compiler bug (found using
;; ; Allegro CL 8.0, but told by Franz support that it still exists in Allegro CL
;; ; 9.0).

;;                       (and last-value (null signal) val)))
;;                  (pc-main-loop
;;                   (if (consp instr-list)
;;                       (cdr instr-list)
;;                     instr-list)
;;                   quit-conditions
;;                   new-last-value
;;                   pc-print-prompt-and-instr-flg
;;                   state)))))))))))

;; (defun pc-single-step (raw-instr state)
;;   ;;   We assume that raw-instr is an "official" instr.
;;   ;; same as pc-single-step-1, except that we deal with atomic macro commands
;;   (declare (xargs :guard (consp raw-instr)))
;;   (let ((tp (pc-command-type (car raw-instr))))
;;     (if (eq tp 'atomic-macro)
;;         (let* ((saved-ss (state-stack))
;;                (old-len (length saved-ss)))
;;           (mv-let (erp val state)
;;                   (pc-single-step-1 raw-instr state)
;;                   (let* ((new-ss (state-stack))
;;                          (new-len (length new-ss))
;;                          (diff (- new-len old-len)))
;;                     (if (and (< old-len new-len)
;;                              (equal saved-ss (nthcdr diff new-ss)))
;;                         (pprogn (pc-assign
;;                                  state-stack
;;                                  (cons (change pc-state
;;                                                (car new-ss)
;;                                                :instruction
;;                                                (make-pretty-pc-instr raw-instr)
;;                                                :local-tag-tree
;;                                                (union-lastn-pc-tag-trees
;;                                                 diff new-ss nil))
;;                                        saved-ss))
;;                                 ;; Notice that atomic macros can "return errors"
;;                                 ;; even when they "fail".
;;                                 (mv erp val state))
;;                       (mv erp val state)))))
;;       (pc-single-step-1 raw-instr state))))
