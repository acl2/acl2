; Patch file described in :DOC developers-guide-example
; Matt Kaufmann, March 2023
; Copyright (C) 2023, ForrestHunt, Inc.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; ACL2 sources before this patch:
; git hash 55d5fff82d920f9cd42943aa26cf58d44d6a333d

; ACL2 sources after this patch:
; git hash 55f20c02c15f9a2d7626060d7381eed3fc849933

;;; Added set-warnings-as-errors to chk-acl2-exports exceptions.

(defun output-ignored-p (token state)
  (member-eq token
             (f-get-global 'inhibit-output-lst state)))

(defconst *initial-global-table*

; Warning: Keep this list in alphabetic order as per ordered-symbol-alistp.  It
; must satisfy the predicate ordered-symbol-alistp if build-state is to build a
; state-p.

; When you add a new state global to this table, consider whether to modify
; *protected-system-state-globals*.

; Note that check-state-globals-initialized insists that all state globals that
; are bound by the build are bound in this alist or in
; *initial-ld-special-bindings*.

  `((abbrev-evisc-tuple . :default)
    (abort-soft . t)
    (accumulated-ttree . nil) ; just what succeeded; tracking the rest is hard
    (acl2-raw-mode-p . nil)
    (acl2-sources-dir .

; This variable is not (as of this writing) used in our own sources.  But it
; could be convenient for users.  In particular, it is used (starting
; mid-October, 2014) by the XDOC system to find the location of the ACL2
; sources graphics/ subdirectory.

                      nil) ; set by initialize-state-globals
    (acl2-version .

; Keep this value in sync with the value assigned to
; acl2::*copy-of-acl2-version* in file acl2.lisp.

; The reason MCL needs special treatment is that (char-code #\Newline) = 13 in
; MCL, not 10.  See also :DOC version.

; ACL2 Version 8.5

; We put the version number on the line above just to remind ourselves to bump
; the value of state global 'acl2-version, which gets printed in .cert files.

; Leave this here.  It is read when loading acl2.lisp.  This constant should be
; a string containing at least one `.'.  The function save-acl2-in-gcl in
; acl2-init.lisp suggests that the user see :doc notexxx, where xxx is the
; substring appearing after the first `.'.

; We have occasion to write fixed version numbers in this code, that is,
; version numbers that are not supposed to be touched when we do ``version
; bump.''  The problem is that version bump tends to replace the standard
; version string with an incremented one, so we need a way to make references
; to versions in some non-standard form.  In Lisp comments we tend to write
; these with an underscore instead of a space before the number.  Thus, `ACL2
; Version_2.5' is a fixed reference to that version.  In :DOC strings we tend
; to write ACL2 Version 2.5.  Note the two spaces.  This is cool because HTML
; etc removes the redundant spaces so the output of this string is perfect.
; Unfortunately, if you use the double space convention in Lisp comments the
; double space is collapsed by ctrl-meta-q when comments are formatted.  They
; are also collapsed by `fill-format-string', so one has to be careful when
; reformatting :DOC comments.

                  ,(concatenate 'string
                                "ACL2 Version 8.5"
                                #+non-standard-analysis
                                "(r)"
                                #+(and mcl (not ccl))
                                "(mcl)"))
    (acl2-world-alist . nil)
    (acl2p-checkpoints-for-summary . nil)
    (axiomsp . nil)
    (bddnotes . nil)
    (book-hash-alistp . nil) ; set in LP
    (boot-strap-flg .

; Keep this state global in sync with world global of the same name.  We expect
; both this and the corresponding world global both to be constant, except when
; both are changed from t to nil during evaluation of exit-boot-strap-mode.
; The state global can be useful for avoiding potentially slow calls of
; getprop, for example as noticed by Sol Swords in function make-event-fn2.
; While we could probably fix many or most such calls by suitable binding of
; the world global, it seems simple and reasonable to record the value in this
; corresponding state global.

                    t)
    (brr-evisc-tuple-initialized . nil)
    (cert-data . nil)
    (certify-book-info .

; Certify-book-info is non-nil when certifying a book, in which case it is a
; certify-book-info record.

                       nil)
    (check-invariant-risk . :WARNING)
    (check-sum-weirdness . nil)
    (checkpoint-forced-goals . nil) ; default in :doc
    (checkpoint-processors . ; avoid unbound var error with collect-checkpoints
                           ,*initial-checkpoint-processors*)
    (checkpoint-summary-limit . (nil . 3))
    (compiled-file-extension . nil) ; set by initialize-state-globals
    (compiler-enabled . nil) ; Lisp-specific; set by initialize-state-globals
    (connected-book-directory . nil)  ; set-cbd couldn't have put this!
    (current-acl2-world . nil)
    (current-package . "ACL2")
    (debug-pspv .

; This variable is used with #+acl2-par for printing information when certain
; modifications are made to the pspv in the waterfall.  David Rager informs us
; in December 2011 that he hasn't used this variable in some time, but that it
; still works as far as he knows.  It should be harmless to remove it if there
; is a reason to do so, but of course there would be fallout from doing so
; (e.g., argument lists of various functions that take a debug-pspv argument
; would need to change).

                nil)
    (debugger-enable . nil) ; keep in sync with :doc set-debugger-enable
    (defaxioms-okp-cert . t) ; t when not inside certify-book
    (deferred-ttag-notes . :not-deferred)
    (deferred-ttag-notes-saved . nil)
    (dmrp . nil)
    (evisc-hitp-without-iprint . nil)
    (eviscerate-hide-terms . nil)
    (fast-cert-status . nil)
    (fmt-hard-right-margin . ,*fmt-hard-right-margin-default*)
    (fmt-soft-right-margin . ,*fmt-soft-right-margin-default*)
    (gag-mode . nil) ; set in lp
    (gag-mode-evisc-tuple . nil)
    (gag-state . nil)
    (gag-state-saved . nil) ; saved when gag-state is set to nil
    (get-internal-time-as-realtime . nil) ; seems harmless to change
    (giant-lambda-object . nil)
    (global-ctx . nil)
    (global-enabled-structure . nil) ; initialized in enter-boot-strap-mode
    (gstackp . nil)
    (guard-checking-on . t)
    (host-lisp . nil)
    (ignore-cert-files . nil)
    (illegal-to-certify-message . nil)
    (in-local-flg . nil)
    (in-prove-flg . nil)
    (in-verify-flg . nil) ; value can be set to the ld-level
    (including-uncertified-p . nil) ; valid only during include-book
    #+acl2-infix (infixp . nil) ; See the Essay on Infix below
    (inhibit-er-hard . nil)
    (inhibit-output-lst . (summary)) ; Without this setting, initialize-acl2
                                     ; will print a summary for each event.
                                     ; Exit-boot-strap-mode sets this list
                                     ; to nil.
    (inhibit-output-lst-stack . nil)
    (inhibited-summary-types . nil)
    (inside-progn-fn1 . nil)
    (inside-skip-proofs . nil)
    (iprint-ar . ,(init-iprint-ar *iprint-hard-bound-default* nil))
    (iprint-fal . nil)
    (iprint-hard-bound . ,*iprint-hard-bound-default*)
    (iprint-soft-bound . ,*iprint-soft-bound-default*)
    (keep-tmp-files . nil)
    (last-event-data . nil)
    (last-make-event-expansion . nil)
    (last-step-limit . -1) ; any number should be OK
    (ld-history . nil)
    (ld-level . 0)
    (ld-okp . :default) ; see :DOC calling-ld-in-bad-contexts
    (ld-redefinition-action . nil)
    (ld-skip-proofsp . nil)
    (logic-fns-with-raw-code . ,*initial-logic-fns-with-raw-code*)
    (macros-with-raw-code . ,*initial-macros-with-raw-code*)
    (main-timer . 0)
    (make-event-debug . nil)
    (make-event-debug-depth . 0)
    (match-free-error . nil) ; if t, modify :doc for set-match-free-error
    (modifying-include-book-dir-alist . nil)
    (parallel-execution-enabled . nil)
    (parallelism-hazards-action . nil) ; nil or :error, else treated as :warn
    (pc-erp . nil)
    (pc-info . nil) ; set in LP
    (pc-output . nil)
    (pc-ss-alist . nil)
    (pc-val . nil)
    (port-file-enabled . t)
    (ppr-flat-right-margin . 40)
    (print-base . 10)
    (print-case . :upcase)
    (print-circle . nil)
    (print-circle-files . t) ; set to nil for #+gcl in LP
    (print-clause-ids . nil)
    (print-escape . t)
    (print-gv-defaults . nil)
    (print-length . nil)
    (print-level . nil)
    (print-lines . nil)
    (print-pretty . nil) ; default in Common Lisp is implementation dependent
    (print-radix . nil)
    (print-readably . nil)
    (print-right-margin . nil)
    (program-fns-with-raw-code . ,*initial-program-fns-with-raw-code*)
    (prompt-function . default-print-prompt)
    (prompt-memo . nil)
    (proof-tree . nil)
    (proof-tree-buffer-width . ,*fmt-soft-right-margin-default*)
    (proof-tree-ctx . nil)
    (proof-tree-indent . "|  ")
    (proof-tree-start-printed . nil)
    (proofs-co . acl2-output-channel::standard-character-output-0)
    (protect-memoize-statistics . nil)
    (raw-guard-warningp . nil)
    (raw-include-book-dir!-alist . :ignore)
    (raw-include-book-dir-alist . :ignore)
    (raw-proof-format . nil)
    (raw-warning-format . nil)
    (redo-flat-fail . nil)
    (redo-flat-succ . nil)
    (redundant-with-raw-code-okp . nil)
    (retrace-p . nil)
    (safe-mode . nil)
    (save-expansion-file . nil) ; potentially set in LP
    (saved-output-p . nil)
    (saved-output-reversed . nil)
    (saved-output-token-lst . nil)
    (script-mode . nil)
    (serialize-character . nil)
    (serialize-character-system . nil) ; set in LP
    (show-custom-keyword-hint-expansion . nil)
    (skip-notify-on-defttag . nil)
    (skip-proofs-by-system . nil)
    (skip-proofs-okp-cert . t) ; t when not inside certify-book
    (skip-reset-prehistory . nil) ; non-nil skips (reset-prehistory nil)
    (slow-array-action . :break) ; set to :warning in exit-boot-strap-mode
    (splitter-output . t)
    (standard-co . acl2-output-channel::standard-character-output-0)
    (standard-oi . acl2-output-channel::standard-object-input-0)
    (step-limit-record . nil)
    (system-attachments-cache . nil) ; see modified-system-attachments
    (temp-touchable-fns . nil)
    (temp-touchable-vars . nil)
    (term-evisc-tuple . :default)
    (timer-alist . nil)
    (tmp-dir . nil) ; set by lp; user-settable but not much advertised.
    (total-parallelism-work-limit ; for #+acl2-par
     . ,(default-total-parallelism-work-limit))
    (total-parallelism-work-limit-error . t) ; for #+acl2-par
    (trace-co . acl2-output-channel::standard-character-output-0)
    (trace-specs . nil)
    (triple-print-prefix . " ")
    (ttags-allowed . :all)
    (undone-worlds-kill-ring . (nil nil nil))

; By making the above list of nils be of length n you can arrange for ACL2 to
; save n worlds for undoing undos.  If n is 0, no undoing of undos is possible.
; If n is 1, the last undo can be undone.

    (useless-runes . nil)
    (user-home-dir . nil) ; set first time entering lp
    (verbose-theory-warning . t)
    (verify-termination-on-raw-program-okp
     .
     (apply$-lambda apply$-prim plist-worldp-with-formals ilks-plist-worldp))
    (walkabout-alist . nil)
    (warnings-as-errors . nil) ; nil or a warnings-as-errors record
    (waterfall-parallelism . nil) ; for #+acl2-par
    (waterfall-parallelism-timing-threshold
     . 10000) ; #+acl2-par -- microsec limit for resource-and-timing-based mode
    (waterfall-printing . :full) ; for #+acl2-par
    (waterfall-printing-when-finished . nil) ; for #+acl2-par
    (window-interface-postlude
     . "#>\\>#<\\<e(acl2-window-postlude ?~sw ~xt ~xp)#>\\>")
    (window-interface-prelude
     . "~%#<\\<e(acl2-window-prelude ?~sw ~xc)#>\\>#<\\<~sw")
    (window-interfacep . nil)
    (wormhole-name . nil)
    (wormhole-status . nil)
    (write-acl2x . nil)
    (write-bookdata . nil) ; see maybe-write-bookdata
    (write-for-read . nil)
    (writes-okp . t)))

(defconst *initial-untouchable-vars*
  '(temp-touchable-vars
    temp-touchable-fns

    user-home-dir

    acl2-version
    certify-book-info

    connected-book-directory

; Although in-local-flg should probably be untouchable, currently that is
; problematic because the macro LOCAL expands into a form that touches
; in-local-flg.
;    in-local-flg

;   Since in-prove-flg need not be untouchable (currently it is only used by
;   break-on-error), we omit it from this list.  It is used by community book
;   misc/bash.lisp.

    axiomsp

    current-acl2-world
    undone-worlds-kill-ring
    acl2-world-alist
    timer-alist

    main-timer

    wormhole-name

    proof-tree
;   proof-tree-ctx  - used in community book books/cli-misc/expander.lisp

    fmt-soft-right-margin
    fmt-hard-right-margin

; We would like to make the following three untouchable, to avoid
; getting a raw Lisp error in this sort of situation:
;   (f-put-global 'inhibit-output-lst '(a . b) state)
;   (defun foo (x) x)
; But this will take some work so we wait....

;   inhibit-output-lst
;   inhibit-output-lst-stack
;   inhibited-summary-types

    in-verify-flg

    mswindows-drive  ;;; could be conditional on #+mswindows

    acl2-raw-mode-p

    defaxioms-okp-cert
    skip-proofs-okp-cert
    ttags-allowed
    skip-notify-on-defttag

    last-make-event-expansion
    make-event-debug-depth

    ppr-flat-right-margin

; The following should perhaps be untouchable, as they need to remain in sync.
; But they don't affect soundness, so if a user wants to mess with them, we
; don't really need to stop that.  Note that we bind gag-state in
; with-ctx-summarized, via save-event-state-globals, so if we want to make that
; variable untouchable then we need to eliminate the call of
; with-ctx-summarized from the definition of the macro theory-invariant.

;   gag-mode
;   gag-state
;   gag-state-saved

    checkpoint-summary-limit

; ld specials and such:

;   ld-skip-proofsp ;;; used in macro skip-proofs; treat bogus values as t
    ld-redefinition-action
    current-package
    useless-runes
    standard-oi
    standard-co
    proofs-co
    ld-prompt
    ld-missing-input-ok
    ld-pre-eval-filter
    ld-pre-eval-print
    ld-post-eval-print
    ld-evisc-tuple
    ld-error-triples
    ld-error-action
    ld-query-control-alist
    ld-verbose

    ld-history

    writes-okp
    program-fns-with-raw-code
    logic-fns-with-raw-code
    macros-with-raw-code
    dmrp
    trace-specs
    retrace-p
    parallel-execution-enabled
    total-parallelism-work-limit ; for #+acl2p-par
    total-parallelism-work-limit-error ; for #+acl2p-par
    waterfall-parallelism ; for #+acl2p-par
    waterfall-printing ; for #+acl2p-par
    redundant-with-raw-code-okp

; print control variables

    print-base   ; must satisfy print-base-p
    print-case   ; :upcase or :downcase (could also support :capitalize)
;   print-circle ; generalized boolean
;   print-circle-files ; generalized boolean
;   print-escape ; generalized boolean
    print-length ; nil or non-negative integer
    print-level  ; nil or non-negative integer
    print-lines  ; nil or non-negative integer
;   print-pretty ; generalized boolean
;   print-radix  ; generalized boolean
;   print-readably ; generalized boolean
    print-right-margin ; nil or non-negative integer
    iprint-ar
    iprint-fal
    iprint-hard-bound
    iprint-soft-bound
;   ld-evisc-tuple ; already mentioned above
    term-evisc-tuple
    abbrev-evisc-tuple
    gag-mode-evisc-tuple
    serialize-character
    serialize-character-system

; others

    skip-proofs-by-system
    host-lisp
    compiler-enabled
    compiled-file-extension
    modifying-include-book-dir-alist
    raw-include-book-dir!-alist raw-include-book-dir-alist
    deferred-ttag-notes
    deferred-ttag-notes-saved
    pc-assign
    illegal-to-certify-message
    acl2-sources-dir
    including-uncertified-p
    check-invariant-risk ; set- function ensures proper values
    print-gv-defaults
    global-enabled-structure
    cert-data
    verify-termination-on-raw-program-okp
    prompt-memo
    system-attachments-cache
    fast-cert-status
    inside-progn-fn1
    warnings-as-errors
    ))

(defrec warnings-as-errors
  (default . alist)
  nil)

(defabbrev warnings-as-errors-default (x)
  (and x ; else default is nil
       (access warnings-as-errors x :default)))

(defabbrev warnings-as-errors-alist (x)
  (and x ; else alist is nil
       (access warnings-as-errors x :alist)))

(defun set-warnings-as-errors-alist (strings flg alist
                                     uninhibited-warning-summaries)

; Note that this code is fine even in the presence of duplicates (up to case)
; in strings, or even a member of strings that is a key (up to case) in alist.
; We simply update the alist with the new, duplicate string while deleting the
; corresponding old key; so the final alist has keys that are duplicate-free up
; to case.

  (cond ((endp strings) alist)
        ((member-string-equal (car strings) uninhibited-warning-summaries)
         (er hard 'set-warnings-as-errors
             "It is illegal to specify that warnings of type ~x0 are to be ~
              converted to errors, because ~x0 is a member (up to case) of ~x1"
             (car strings)
             '*uninhibited-warning-summaries*))
        (t (set-warnings-as-errors-alist
            (cdr strings)
            flg
            (let ((pair (assoc-string-equal (car strings) alist)))
              (cond ((and (consp pair)
                          (eq (cdr pair) flg))
                     alist)
                    ((null pair)
                     (acons (car strings) flg alist))
                    (t
                     (acons (car strings)
                            flg
                            (remove1-assoc-string-equal (car strings)
                                                        alist)))))
            uninhibited-warning-summaries))))

(defun set-warnings-as-errors (flg strings state)

; If strings is :all then we reset to make that the default.

  (declare (xargs :guard (member-eq flg '(t nil :always))))
  (cond
   ((eq strings :all)
    (f-put-global 'warnings-as-errors
                  (make warnings-as-errors :default flg :alist nil)
                  state))
   ((string-listp strings)
    (let* ((old (f-get-global 'warnings-as-errors state))
           (default (warnings-as-errors-default old))
           (alist (warnings-as-errors-alist old)))
      (cond ((and (eq flg default)
                  (null (assoc-string-equal (car strings) alist)))
             state)
            (t (f-put-global 'warnings-as-errors
                             (if old
                                 (change warnings-as-errors
                                         old
                                         :alist
                                         (set-warnings-as-errors-alist
                                          strings flg alist
                                          *uninhibited-warning-summaries*))
                               (make warnings-as-errors
                                     :default nil
                                     :alist
                                     (set-warnings-as-errors-alist
                                      strings flg alist
                                      *uninhibited-warning-summaries*)))
                             state)))))
   (t (prog2$ (er hard 'set-warnings-as-errors
                  "Illegal second argument of ~x0, ~x1: must be :ALL or a ~
                   list of strings."
                  'set-warnings-as-errors
                  strings)
              state))))

(defrec state-vars

; Warning: Keep this in sync with default-state-vars.

; Note that do-expressionp is not actually a state global, even though most
; fields do name a state global.  That's OK, as we are careful about this in
; default-state-vars.  Also note that its value is either nil or a
; do-expressionp record.

  (((safe-mode . boot-strap-flg) . (temp-touchable-vars . guard-checking-on))
   .
   ((ld-skip-proofsp . temp-touchable-fns) .
    ((parallel-execution-enabled . in-macrolet-def)
     do-expressionp warnings-as-errors . inhibit-output-lst)))
  nil)

(defun-one-output enter-boot-strap-mode (system-books-dir operating-system)

; If we interrupted an earlier initialization, the following form will undo it.
; This will set the *acl2-unwind-protect-stack* to nil because *ld-level* is
; 0 at the top.

  (acl2-unwind *ld-level* nil)

; Now provide a frame into which the set-w can push its acl2-unwind-protect
; forms.  An abort of the set-w will leave the forms in the frame so that the
; above acl2-unwind will undo them upon the next initialization attempt.  But
; if the set-w is successful, it will leave the then empty frame on the stack.

  (push nil *acl2-unwind-protect-stack*)
  (set-w 'retraction nil *the-live-state*)
  (do-symbols (sym (find-package "ACL2_GLOBAL_ACL2"))
              (makunbound sym))
  (do-symbols (sym (find-package
                    (concatenate 'string
                                 *global-package-prefix*
                                 *main-lisp-package-name*)))
              (makunbound sym))
  (do-symbols (sym (find-package "ACL2_GLOBAL_KEYWORD"))
              (makunbound sym))
  (initialize-state-globals)

; The following patch for save-gprof.lsp may be more heavy-handed than
; necessary, because maybe we don't need to keep all TMP* files.  See also
; "Note: temporary files" in save-gprof.lsp.

; If we want to let the user set other variables, we could replace
; user::*acl2-keep-tmp-files* with a variable whose value associates state
; global symbol names with initial values.  But then we will need to check that
; none is untouchable, and we will need to make a corresponding change in
; save-gprof.lsp.

  #+gcl
  (f-put-global 'keep-tmp-files user::*acl2-keep-tmp-files* *the-live-state*)
  (f-put-global 'global-enabled-structure
                (initial-global-enabled-structure "ENABLED-ARRAY-")
                *the-live-state*)
  (f-put-ld-specials *initial-ld-special-bindings*
                     nil ; no changes to useless-runes (not an LD special)
                     *the-live-state*)

; The next set-w will avail itself of the empty frame left above.

  (let ((project-dir-alist
         (acons :system
                (cond
                 (system-books-dir
                  (let* ((dir (unix-full-pathname
                               (cond
                                ((symbolp system-books-dir)
                                 (symbol-name system-books-dir))
                                ((stringp system-books-dir)
                                 system-books-dir)
                                (t (er hard 'initialize-acl2
                                       "Unable to complete initialization, ~
                                        because the supplied system books ~
                                        directory, ~x0, is not a string."
                                       system-books-dir)))))
                         (msg (bad-lisp-stringp dir)))
                    (when msg
                      (interface-er
                       "The value of the system-books-dir argument of ~
                        ENTER-BOOT-STRAP-MODE, which is ~x0, is not a legal ~
                        ACL2 string.~%~@1"
                       dir msg))
                    (canonical-dirname! (maybe-add-separator dir)
                                        'enter-boot-strap-mode
                                        *the-live-state*)))
                 (t (concatenate
                     'string
                     (canonical-dirname! (our-pwd)
                                         'enter-boot-strap-mode
                                         *the-live-state*)
                     "books/")))
                nil)))
    (set-w 'extension
           (primordial-world operating-system project-dir-alist)
           *the-live-state*))

; Inhibit proof-tree output during the build, including pass-2 if present.
; Warning: If you change this, make the corresponding change in
; default-state-vars.

  (f-put-global 'inhibit-output-lst '(proof-tree) *the-live-state*)

; We now pop the empty frame.  There is no way this acl2-unwind will do any
; real work because only an abort would leave stuff in the frame and an abort
; would prevent us from getting here.  Note that in the scheme of things,
; namely within the control structure of initialize-acl2, it is strictly
; unnecessary for us to pop this empty frame: each LD called by initialize-acl2
; will unwind the stack back to nil.  But I do it here out of politeness: the
; stack started empty and ends that way.

  (acl2-unwind *ld-level* nil))

(defconst *default-state-vars*

; Warning: if you change this definition, then change the defaults for the &key
; parameters accordingly in the definition of macro default-state-vars.

  (make state-vars
        :guard-checking-on t
        :inhibit-output-lst '(proof-tree)))

(defmacro default-state-vars

; Warning: if you change the defaults for the &key parameters below, change the
; definition of *default-state-vars* accordingly.

    (state-p &rest args
             &key
             (safe-mode 'nil safe-mode-p)
             (boot-strap-flg 'nil boot-strap-flg-p)
             (temp-touchable-vars 'nil temp-touchable-vars-p)
             (guard-checking-on 't guard-checking-on-p)
             (ld-skip-proofsp 'nil ld-skip-proofsp-p)
             (temp-touchable-fns 'nil temp-touchable-fns-p)
             (parallel-execution-enabled 'nil parallel-execution-enabled-p)
             (in-macrolet-def ; not a state global, so avoid f-get-global below
              'nil)
             (do-expressionp ; not a state global, so avoid f-get-global below
              'nil)
             (warnings-as-errors 'nil warnings-as-errors-p)
; Warning: If you change '(proof-tree) just below, make the corresponding
; change in enter-boot-strap-mode.
             (inhibit-output-lst ''(proof-tree) inhibit-output-lst-p))

; Warning: Keep this in sync with defrec state-vars.

; State-p is t to indicate that we use the current values of the relevant state
; globals.  Otherwise we use the specified defaults, which are supplied above
; for convenience but can be changed there (i.e., in this code) if better
; default values are found.

  (cond ((eq state-p t)
         `(make state-vars
                :safe-mode
                ,(if safe-mode-p
                     safe-mode
                   '(f-get-global 'safe-mode state))
                :boot-strap-flg
                ,(if boot-strap-flg-p
                     boot-strap-flg
                   '(f-get-global 'boot-strap-flg state))
                :temp-touchable-vars
                ,(if temp-touchable-vars-p
                     temp-touchable-vars
                   '(f-get-global 'temp-touchable-vars state))
                :guard-checking-on
                ,(if guard-checking-on-p
                     guard-checking-on
                   '(f-get-global 'guard-checking-on state))
                :ld-skip-proofsp
                ,(if ld-skip-proofsp-p
                     ld-skip-proofsp
                   '(f-get-global 'ld-skip-proofsp state))
                :temp-touchable-fns
                ,(if temp-touchable-fns-p
                     temp-touchable-fns
                   '(f-get-global 'temp-touchable-fns state))
                :parallel-execution-enabled
                ,(if parallel-execution-enabled-p
                     parallel-execution-enabled
                   '(f-get-global 'parallel-execution-enabled state))
                :in-macrolet-def
                ,in-macrolet-def
                :do-expressionp
                ,do-expressionp
                :warnings-as-errors
                ,(if warnings-as-errors-p
                     warnings-as-errors
                   '(f-get-global 'warnings-as-errors state))
                :inhibit-output-lst
                ,(if inhibit-output-lst-p
                     inhibit-output-lst
                   '(f-get-global 'inhibit-output-lst state))))
        ((null args)
         '*default-state-vars*)
        (t ; state-p is not t
         `(make state-vars
                :safe-mode ,safe-mode
                :boot-strap-flg ,boot-strap-flg
                :temp-touchable-vars ,temp-touchable-vars
                :guard-checking-on ,guard-checking-on
                :ld-skip-proofsp ,ld-skip-proofsp
                :temp-touchable-fns ,temp-touchable-fns
                :parallel-execution-enabled ,parallel-execution-enabled
                :warnings-as-errors ,warnings-as-errors
                :inhibit-output-lst ,inhibit-output-lst))))

(defun warnings-as-errors-val-guard (summary warnings-as-errors)
  (declare (xargs :guard t))
  (and (or (null summary)
           (and (stringp summary)
                (standard-string-p summary)))
       (or (null warnings-as-errors)
           (and (weak-warnings-as-errors-p warnings-as-errors)
                (standard-string-alistp
                 (warnings-as-errors-alist warnings-as-errors))))))

(defun warnings-as-errors-val (summary warnings-as-errors)
  (declare (xargs :guard
                  (warnings-as-errors-val-guard summary warnings-as-errors)))
  (let* ((pair
          (and summary
               (assoc-string-equal summary (warnings-as-errors-alist
                                            warnings-as-errors))))
         (erp (if pair
                  (cdr pair)
                (warnings-as-errors-default warnings-as-errors))))
    (if (booleanp erp)
        erp
      :always)))

(defun warning1-cw (ctx summary str alist wrld state-vars)

; This function has the same effect as warning1, except that printing is in a
; wormhole and hence doesn't modify state.

  (declare (xargs :guard (and (or (null summary)
                                  (let ((summary ; could be ("Use"), e.g.
                                         (if (consp summary)
                                             (car summary)
                                           summary)))
                                    (and (stringp summary)
                                         (standard-string-p summary))))
                              (alistp alist)
                              (plist-worldp wrld)
                              (standard-string-alistp
                               (table-alist 'inhibit-warnings-table wrld))
                              (weak-state-vars-p state-vars))))
  (warning1-form t))

;;; Added new fn
#-(or acl2-loop-only gcl)
(declaim

; This declaim form avoids warnings that would otherwise be generated during
; the boot-strap (in CCL, at least) by ec-call.  We don't bother in GCL because
; the declaim form itself has caused a warning!

 (ftype function
        acl2_*1*_acl2::apply$
        acl2_*1*_acl2::rewrite-rule-term-exec
        acl2_*1*_acl2::linear-lemma-term-exec
        acl2_*1*_acl2::conjoin
        acl2_*1*_acl2::pairlis$
        acl2_*1*_acl2::close-input-channel
        acl2_*1*_acl2::warnings-as-errors-val
        acl2_*1*_acl2::member-equal))

;;; In boot-strap-pass-2-a.lisp:
(verify-termination-boot-strap warnings-as-errors-val-guard) ; and guards
(verify-termination-boot-strap warnings-as-errors-val) ; and guards

(defmacro warning1-form (commentp)

; See warning1.

  (declare (xargs :guard ; avoid capture
                  (not (or (eq commentp 'warnings-as-errors-val)
                           (eq commentp 'check-warning-off)
                           (eq commentp 'summary)))))
  `(mv-let (check-warning-off summary)
     (cond ((consp summary)
            (mv nil (car summary)))
           (t (mv t summary)))
     (let ((warnings-as-errors-val
            ,(if commentp
                 `(ec-call ; for guard verification of warning1-cw
                   (warnings-as-errors-val
                    summary
                    (access state-vars state-vars :warnings-as-errors)))
               `(warnings-as-errors-val
                 summary
                 (f-get-global 'warnings-as-errors state)))))
       (cond
        ((and (eq warnings-as-errors-val :always)
              (not (member-string-equal summary
                                        *uninhibited-warning-summaries*)))
         (let ((str (cond ((consp str) ; see handling of str+ in warning1-body
                           (car str))
                          (t str))))

; We do not use io? here, because when commentp holds, io? makes a wormhole
; call that seems to avoid avoiding having the throw from hard-error go all the
; way to the top level.

           ,(cond
             (commentp
              `(and (not (ec-call ; for guard verification of warning1-cw
                          (member-equal 'error
                                        (access state-vars state-vars
                                                :inhibit-output-lst))))
                    (hard-error ctx (cons summary str) alist)))
             (t `(prog2$
                  (and (not (member-eq 'error
                                       (f-get-global 'inhibit-output-lst
                                                     state)))
                       (hard-error ctx (cons summary str) alist))
                  state)))))
        ((and check-warning-off
              (not (member-string-equal summary
                                        *uninhibited-warning-summaries*))
              ,(if commentp
                   '(or (ec-call ; for guard verification of warning1-cw
                         (member-equal 'warning
                                       (access state-vars state-vars
                                               :inhibit-output-lst)))
                        (warning-off-p1 summary
                                        wrld
                                        (access state-vars state-vars
                                                :ld-skip-proofsp)))
                 '(or (member-eq 'warning
                                 (f-get-global 'inhibit-output-lst state))
                      (warning-off-p summary state))))
         ,(if commentp nil 'state))
        ((and warnings-as-errors-val
              (not (member-string-equal summary
                                        *uninhibited-warning-summaries*)))
         (let ((str (cond ((consp str) ; see handling of str+ in warning1-body
                           (car str))
                          (t str))))
; See comment above about not usingn io?.
           ,(cond
             (commentp
              `(and (not (ec-call ; for guard verification of warning1-cw
                          (member-equal 'error
                                        (access state-vars state-vars
                                                :inhibit-output-lst))))
                    (hard-error ctx (cons summary str) alist)))
             (t `(prog2$ (and (not (member-eq 'error
                                              (f-get-global 'inhibit-output-lst
                                                            state)))
                              (hard-error ctx (cons summary str) alist))
                         state)))))

; Note:  There are two io? expressions below.  They are just alike except
; that the first uses the token WARNING! and the other uses WARNING.  Keep
; them that way!

        ((and summary
              (member-string-equal summary *uninhibited-warning-summaries*))
         (io? WARNING! ,commentp state
              (summary ctx alist str)
              (warning1-body ctx summary str alist state)
              :chk-translatable nil))
        (t (io? WARNING ,commentp state
                (summary ctx alist str)
                (warning1-body ctx summary str alist state)
                :chk-translatable nil))))))

(defmacro warning-disabled-p (summary)

; We can use this utility to avoid needless computation on behalf of disabled
; warnings.

  (declare (xargs :guard (stringp summary)))
  (let ((tp (if (member-equal summary *uninhibited-warning-summaries*)
                'warning!
              'warning)))
    `(and (or (output-ignored-p ',tp state)
              (warning-off-p ,summary state))

; Allow warning$ to be called even when it would normally be suppressed, if the
; warning is to be converted unconditionally to an error.

          (not (eq (warnings-as-errors-val
                    ,summary
                    (f-get-global 'warnings-as-errors state))
                   :always)))))

(defun include-book-fn (user-book-name state
                                       load-compiled-file
                                       expansion-alist/cert-data
                                       uncertified-okp
                                       defaxioms-okp
                                       skip-proofs-okp
                                       ttags
                                       dir
                                       event-form)

; Note that the acl2-defaults-table is initialized when raising the portcullis.
; As of this writing, this happens by way of a call of chk-certificate-file in
; include-book-fn1, as chk-certificate-file calls chk-certificate-file1, which
; calls chk-raise-portcullis, etc.

; When this function is called by certify-book-fn, expansion-alist/cert-data is
; (cons E C), where E an expansion-alist generated from make-event calls and C
; is cert-data extracted from pass1.  Otherwise, expansion-alist/cert-data is
; nil.

  (with-ctx-summarized
   (make-ctx-for-event event-form (cons 'include-book user-book-name))
   (state-global-let*
    ((compiler-enabled (f-get-global 'compiler-enabled state))
     (port-file-enabled (f-get-global 'port-file-enabled state))
     (warnings-as-errors nil))
    (pprogn
     (cond ((and (not (eq load-compiled-file :default))
                 (not (eq load-compiled-file nil))
                 (not (f-get-global 'compiler-enabled state)))
            (warning$ ctx "Compiled file"
                      "Ignoring value ~x0 supplied for include-book keyword ~
                       parameter :LOAD-COMPILED-FILE, treating it as ~x1 ~
                       instead, because of an earlier evaluation of ~x2; see ~
                       :DOC compilation."
                      load-compiled-file
                      nil
                      '(set-compiler-enabled nil state)))
           (t state))
     (er-let* ((dir-value
                (cond (dir (include-book-dir-with-chk soft ctx dir))
                      (t (value (cbd))))))
       (mv-let
         (full-book-string full-book-name directory-name familiar-name)
         (parse-book-name dir-value user-book-name ".lisp" ctx state)
         (er-progn
          (chk-input-object-file full-book-string ctx state)
          (chk-include-book-inputs load-compiled-file
                                   uncertified-okp
                                   defaxioms-okp
                                   skip-proofs-okp
                                   ctx state)
          (state-global-let*
           ((ignore-cert-files (or (f-get-global 'ignore-cert-files state)
                                   (and (eq uncertified-okp :ignore-certs)
                                        full-book-name))))
           (let* ((behalf-of-certify-flg
                   (not (null expansion-alist/cert-data)))
                  (load-compiled-file0 load-compiled-file)
                  (load-compiled-file (and (f-get-global 'compiler-enabled
                                                         state)
                                           load-compiled-file))
                  (cddr-event-form
                   (if (and event-form
                            (eq load-compiled-file0
                                load-compiled-file))
                       (cddr event-form)
                     (append
                      (if (not (eq load-compiled-file
                                   :default))
                          (list :load-compiled-file
                                load-compiled-file)
                        nil)
                      (if (not (eq uncertified-okp t))
                          (list :uncertified-okp
                                uncertified-okp)
                        nil)
                      (if (not (eq defaxioms-okp t))
                          (list :defaxioms-okp
                                defaxioms-okp)
                        nil)
                      (if (not (eq skip-proofs-okp t))
                          (list :skip-proofs-okp
                                skip-proofs-okp)
                        nil)))))
             (cond ((or behalf-of-certify-flg
                        #-acl2-loop-only *hcomp-book-ht*
                        (null load-compiled-file))

; So, *hcomp-book-ht* was previously bound by certify-book-fn or in the other
; case, below.

                    (include-book-fn1
                     user-book-name state load-compiled-file
                     expansion-alist/cert-data
                     uncertified-okp defaxioms-okp skip-proofs-okp
                     ttags
; The following were bound above:
                     ctx full-book-string full-book-name
                     directory-name familiar-name cddr-event-form))
                   (t
                    (let #+acl2-loop-only ()
                         #-acl2-loop-only
                         ((*hcomp-book-ht* (make-hash-table :test 'equal)))

; Populate appropriate hash tables; see the Essay on Hash Table Support for
; Compilation.  It may be tempting to move this call of include-book-raw-top
; into include-book-fn1, for example to print ttag notes before potentially
; redefining print-ttag-note as a no-op; but that is probably would not be
; helpful, since we probably want include-book-raw-top to (continue to)
; populate hash tables before evaluation of the portcullis commands, but ttag
; information is read from the certificate after that evaluation.

                         #-acl2-loop-only
                         (include-book-raw-top full-book-string full-book-name
                                               directory-name
                                               load-compiled-file dir ctx state)
                         (include-book-fn1
                          user-book-name state load-compiled-file
                          expansion-alist/cert-data
                          uncertified-okp defaxioms-okp skip-proofs-okp
                          ttags
; The following were bound above:
                          ctx full-book-string full-book-name
                          directory-name familiar-name
                          cddr-event-form)))))))))))))

(defun certify-book-fn (user-book-name k compile-flg defaxioms-okp
                                       skip-proofs-okp ttags ttagsx ttagsxp
                                       acl2x write-port pcert
                                       useless-runes-r/w useless-runes-r/w-p
                                       state)

; For a discussion of the addition of hidden defpkg events to the portcullis,
; see the Essay on Hidden Packages Added by Certify-book, above.  Also see the
; Essay on Fast-cert for discussion pertaining to fast-cert mode.

  (with-ctx-summarized
   (make-ctx-for-event
    (list* 'certify-book user-book-name
           (if (and (equal k 0) (eq compile-flg :default))
               nil
             '(irrelevant)))
    (cons 'certify-book user-book-name))
   (state-global-let*
    ((warnings-as-errors nil))
    (save-parallelism-settings
     (let ((wrld0 (w state)))
       (cond
        ((not (eq (caar wrld0) 'COMMAND-LANDMARK))

; If we remove this restriction, then we need to change get-portcullis-cmds (at
; the least) so as not to look only for command markers.

         (er soft ctx
             "Certify-book can only be run at the top-level, either directly ~
              in the top-level loop or at the top level of LD."))
        ((and (stringp user-book-name)
              (let ((len (length user-book-name)))
                (and (<= 10 len) ; 10 = (length "@expansion")
                     (equal (subseq user-book-name (- len 10) len)
                            "@expansion"))))
         (er soft ctx
             "Book filenames may not end in \"@expansion\"."))
        ((not (booleanp acl2x)) ; also checked in certify-book guard
         (er soft ctx
             "The argument :ACL2X for certify-book must take on the value of ~
              T or NIL.  The value ~x0 is thus illegal.  See :DOC ~
              certify-book."
             acl2x))
        (t
         (er-let* ((pcert-env (cond ((eq pcert :default)
                                     (getenv! "ACL2_PCERT_ARG" state))
                                    (t (value nil))))
                   (pcert (cond ((not pcert-env)
                                 (value (if (eq pcert :default)
                                            nil
                                          pcert)))

; For the remaining cases we know pcert-env is not nil, hence pcert = :default.

                                ((string-equal pcert-env "T")
                                 (value t))
                                (t (value (intern (string-upcase pcert-env)
                                                  "KEYWORD"))))))
           (mv-let
             (full-book-string full-book-name directory-name familiar-name)
             (parse-book-name (cbd) user-book-name ".lisp" ctx state)
             (cond
              ((eq pcert :complete)
               (certify-book-finish-complete full-book-string full-book-name
                                             ctx state))
              (t
               (er-let* ((write-port
                          (cond
                           ((member-eq write-port '(t nil))
                            (value write-port))
                           ((eq write-port :default)
                            (cond
                             (pcert

; We have seen a "convert" failure (for creating the .pcert1 file) for
; community book
; books/workshops/2011/verbeek-schmaltz/sources/correctness.lisp.  The problem
; seems to be that build system automatically creates .port files that are
; loaded, but more .port files are around when building correctness.pcert1 file
; than when building correctness.pcert1.pcert0.  Our solution is to make the
; default for :write-port be nil, instead of t, when doing any step of
; provisional certification -- even when ACL2_WRITE_PORT is set, so as to
; defeat the build system's attempt to build .port files when doing
; pcertification steps.

                              (value nil))
                             (t
                              (er-let* ((str
                                         (getenv! "ACL2_WRITE_PORT" state)))
                                (value (cond (str (intern$ (string-upcase str)
                                                           "ACL2"))
                                             (t t))))))) ; default
                           (t (er soft ctx
                                  "Illegal :write-port argument, ~x0.  See ~
                                   :DOC certify-book."))))
                         (write-acl2x
                          (cond (acl2x (value (f-get-global 'write-acl2x state)))
                                ((f-get-global 'write-acl2x state)
                                 (er soft ctx
                                     "Apparently set-write-acl2x has been ~
                                      evaluated with argument value ~x0, yet ~
                                      certify-book is being called without ~
                                      supplying keyword argument :ACL2X T.  ~
                                      This is illegal.  See :DOC ~
                                      set-write-acl2x.  If you do not intend ~
                                      to write a .acl2x file, you may wish to ~
                                      evaluate ~x1."
                                     (f-get-global 'write-acl2x state)
                                     '(set-write-acl2x nil state)))
                                (t (value nil))))
                         (cert-op (cond ((and write-acl2x pcert)
                                         (er soft ctx
                                             "It is illegal to specify the ~
                                              writing  of a .acl2x file when ~
                                              a non-nil value for :pcert ~
                                              (here, ~x1) is specified~@0."
                                             pcert
                                             (cond (pcert-env
                                                    " (even when the :pcert ~
                                                     argument is supplied, as ~
                                                     in this case, by an ~
                                                     environment variable)")
                                                   (t ""))))
                                        (write-acl2x
                                         (value (if (consp write-acl2x)
                                                    :write-acl2xu
                                                  :write-acl2x)))
                                        (t (case pcert
                                             (:create (value :create-pcert))
                                             (:convert (value :convert-pcert))
                                             ((t) (value :create+convert-pcert))
                                             ((nil) (value t))
                                             (otherwise
                                              (er soft ctx
                                                  "Illegal value of :pcert, ~
                                                   ~x0~@1.  See :DOC ~
                                                   certify-book."
                                                  pcert
                                                  (cond
                                                   (pcert-env
                                                    (msg " (from environment ~
                                                         variable ~
                                                         ACL2_PCERT_ARG=~x0"
                                                         pcert-env))
                                                   (t ""))))))))
                         (skip-proofs-okp
                          (value (cond ((eq skip-proofs-okp :default)
                                        (consp write-acl2x))
                                       (t skip-proofs-okp))))
                         (uncertified-okp (value (consp write-acl2x)))
                         (ttagsx (value (if ttagsxp ttagsx ttags)))
                         (ttags (cond ((and ttagsxp (not acl2x))
                                       (er soft ctx
                                           "The  :TTAGSX argument for ~
                                            certify-book may only be supplied ~
                                            if :ACL2X is T.  See :DOC ~
                                            set-write-acl2x."))
                                      (t (chk-well-formed-ttags
                                          (cond (write-acl2x ttagsx)
                                                (t ttags))
                                          (cbd) ctx state))))
                         (pair0 (chk-acceptable-ttags1

; We check whether the ttags in the certification world are legal for the given
; ttags, and if so we refine ttags, as described in chk-acceptable-ttag1.

                                 (global-val 'ttags-seen wrld0)
                                 nil ; correct active-book-name, but irrelevant
                                 ttags
                                 nil    ; irrelevant value for ttags-seen
                                 :quiet ; ttags in cert. world: already reported
                                 ctx state))
                         (certify-book-info-0
                          (value (make certify-book-info
                                       :full-book-name full-book-name
                                       :cert-op cert-op
                                       :include-book-phase nil))))
                 (state-global-let*
                  ((compiler-enabled (f-get-global 'compiler-enabled state))
                   (port-file-enabled (f-get-global 'port-file-enabled state))
                   (certify-book-info certify-book-info-0)
                   (match-free-error nil)
                   (defaxioms-okp-cert defaxioms-okp)
                   (skip-proofs-okp-cert skip-proofs-okp)
                   (guard-checking-on ; see Essay on Guard Checking
                    t))
                  (er-let* ((env-compile-flg
                             (getenv! "ACL2_COMPILE_FLG" state))
                            (compile-flg
                             (cond
                              ((or (and env-compile-flg
                                        (string-equal env-compile-flg "ALL"))
                                   (eq compile-flg :all))
                               (value t))
                              ((or (eq cert-op :convert-pcert)
                                   (null (f-get-global 'compiler-enabled state)))
                               (value nil))
                              ((not (eq compile-flg :default))
                               (value compile-flg))
                              ((or (null env-compile-flg)
                                   (string-equal env-compile-flg "T"))
                               (value t))
                              ((string-equal env-compile-flg "NIL")
                               (value nil))
                              (t (er soft ctx
                                     "Illegal value, ~x0, for environment ~
                                      variable ACL2_COMPILE_FLG.  The legal ~
                                      values are (after converting to ~
                                      uppercase) \"\", \"T\", \"NIL\", \"\", ~
                                      and \"ALL\"."
                                     env-compile-flg))))
                            (saved-acl2-defaults-table
                             (value (table-alist 'acl2-defaults-table
                                                 (w state))))

; If you add more keywords to this list, make sure you do the same to the list
; constructed by include-book-fn.

                            (suspect-book-action-alist
                             (value
                              (list (cons :uncertified-okp uncertified-okp)
                                    (cons :defaxioms-okp defaxioms-okp)
                                    (cons :skip-proofs-okp skip-proofs-okp))))
                            (cert-obj

; The following call can modify (w state) by evaluating portcullis commands
; from an existing certificate file.

                             (chk-acceptable-certify-book
                              user-book-name full-book-string full-book-name
                              directory-name suspect-book-action-alist cert-op k
                              ctx state))
                            (portcullis-cmds0 (value (access cert-obj cert-obj
                                                             :cmds)))
                            (old-useless-runes
                             (value (f-get-global 'useless-runes state)))
                            (useless-runes


; By now, we should have ensured that all portcullis commands have been run
; (consider the case of certify-book with k=t), so that packages are all
; available.

                             (initial-useless-runes full-book-string
                                                    useless-runes-r/w
                                                    useless-runes-r/w-p
                                                    nil ctx state))
                            (ignore (cond (write-port
                                           (write-port-file full-book-string
                                                            portcullis-cmds0
                                                            ctx state))
                                          (t (value nil)))))
                    (let* ((wrld1 ; from chk-acceptable-certify-book
                            (w state))
                           (pre-alist-wrld1
                            (global-val 'include-book-alist wrld1))
                           (wrld1-known-package-alist
                            (global-val 'known-package-alist wrld1))
                           (acl2x-file
                            (convert-book-string-to-acl2x full-book-string))
                           (fast-cert-p0 (fast-cert-p state))
                           (fast-cert-p

; Maybe later we'll support fast-cert for pcert, but not now.

                            (and (not pcert)
                                 fast-cert-p0)))
                      (pprogn
                       (f-put-global 'useless-runes useless-runes state)
                       (io? event nil state
                            (fast-cert-p full-book-string cert-op fast-cert-p0
                                         pcert)
                            (fms "CERTIFICATION ATTEMPT~#h~[~|**using ~
                                  fast-cert mode**~|~/ ~]~@0FOR ~
                                  ~x1~%~s2~@3~%~%*~ Step 1: Read ~x1 and ~
                                  compute its book-hash.~%"
                                 (list (cons #\h (if fast-cert-p 0 1))
                                       (cons #\0
                                             (case cert-op
                                               ((:write-acl2xu :write-acl2x)
                                                "(for writing .acl2x file) ")
                                               (:create-pcert
                                                "(for writing .pcert0 file) ")
                                               (:create+convert-pcert
                                                "(for writing .pcert0 and ~
                                                 .pcert1 files) ")
                                               (:convert-pcert
                                                "(for writing .pcert1 file) ")
                                               (t "")))
                                       (cons #\1 full-book-string)
                                       (cons #\2 (f-get-global 'acl2-version
                                                               state))
                                       (cons #\3 (if (and fast-cert-p0 pcert)
                                                     "~|Note that fast-cert ~
                                                      mode is active but will ~
                                                      be ignored during ~
                                                      certification until ~
                                                      writing the certificate ~
                                                      file."
                                                   "")))
                                 (proofs-co state) state nil))
                       (er-let* ((ev-lst
                                  (let (#-acl2-loop-only
                                        (*acl2-error-msg*
                                         *acl2-error-msg-certify-book-step1*))
                                    (read-object-file full-book-string ctx
                                                      state)))
                                 (acl2x-expansion-alist
; See the Essay on .acl2x Files (Double Certification).
                                  (cond (write-acl2x (value nil))
                                        (t (read-acl2x-file acl2x-file
                                                            full-book-string
                                                            (length ev-lst)
                                                            acl2x ctx state))))
                                 (expansion-alist0
                                  (cond
                                   ((eq cert-op :convert-pcert)
                                    (let ((elided-expansion-alist
                                           (access cert-obj cert-obj
                                                   :expansion-alist)))
                                      (mv-let
                                        (bad-entry elided-entry)
                                        (expansion-alist-conflict
                                         acl2x-expansion-alist
                                         elided-expansion-alist)
                                        (cond
                                         (bad-entry
                                          (er soft ctx
                                              "The following expansion-alist ~
                                               entry from file ~x0 is ~
                                               unexpected:~|~x1~|~@2"
                                              acl2x-file
                                              bad-entry
                                              (cond
                                               (elided-entry
                                                (msg "It was expected to ~
                                                      correspond to the ~
                                                      following entry from ~
                                                      the :expansion-alist in ~
                                                      file ~x0:~|~x1"
                                                     (convert-book-string-to-cert
                                                      full-book-string
                                                      :create-pcert)
                                                     elided-entry))
                                               (t ""))))
                                         (t
                                          (value
                                           (merge-into-expansion-alist
                                            (merge-into-expansion-alist
                                             elided-expansion-alist
                                             acl2x-expansion-alist)
                                            (access cert-obj cert-obj
                                                    :pcert-info))))))))
                                   (t (value acl2x-expansion-alist))))
                                 (ignore
                                  (pprogn
                                   (print-certify-book-step-2
                                    ev-lst expansion-alist0
                                    (and (eq cert-op :convert-pcert)
                                         (convert-book-string-to-cert
                                          full-book-string :create-pcert))
                                    acl2x-file
                                    state)
                                   (value nil)))
                                 (pass1-result
                                  (state-global-let*
                                   ((ttags-allowed (car pair0))
                                    (user-home-dir

; We disallow ~/ in subsidiary include-book forms, because its meaning will be
; different when the superior book is included if the user changes (see :doc
; pathname).  We do not make a similar binding in Step 3, because it calls
; include-book-fn and we do want to allow the argument to certify-book to start
; with ~/.  Step 3 presumably doesn't call any include-book forms not already
; considered in Step 2, so this decision should be OK.

                                     nil)

; We will accumulate into the flag axiomsp whether any axioms have been added,
; starting with those in the portcullis.  We can identify axioms in the
; portcullis by asking if the current nonconstructive axioms are different from
; those at the end of boot-strap.

                                    (axiomsp
                                     (not
                                      (equal
                                       (global-val ; axioms as of boot-strap
                                        'nonconstructive-axiom-names
                                        (scan-to-landmark-number
                                         'event-landmark
                                         (global-val 'event-number-baseline
                                                     wrld1)
                                         wrld1))
                                       (global-val ; axioms now
                                        'nonconstructive-axiom-names
                                        wrld1))))
                                    (ld-redefinition-action nil))
                                   (with-cbd
                                    directory-name
                                    (revert-world-on-error
                                     (er-let* ((portcullis-skipped-proofsp
                                                (value
                                                 (and (global-val
                                                       'skip-proofs-seen
                                                       (w state))
                                                      t)))
                                               (expansion-alist-and-index

; The fact that we are under 'certify-book means that all calls of
; include-book will insist that the :uncertified-okp action is nil, meaning
; errors will be caused if uncertified books are read.

                                                (process-embedded-events
                                                 'certify-book
                                                 saved-acl2-defaults-table
                                                 (or (eq cert-op :create-pcert)
                                                     (and (consp write-acl2x)
                                                          (car write-acl2x)))
                                                 (cadr (car ev-lst))
                                                 (list 'certify-book
                                                       full-book-name)
                                                 (subst-by-position
                                                  expansion-alist0

; See the Essay on .acl2x Files (Double Certification).

                                                  (cdr ev-lst)
                                                  1)
                                                 1 nil nil 'certify-book
                                                 state))
                                               (ignore
                                                (pprogn
                                                 (chk-absstobj-invariants
                                                  state)
                                                 (illegal-to-certify-check
                                                  nil ctx state)))
                                               (expansion-alist
                                                (value
                                                 (cond
                                                  (write-acl2x
                                                   (assert$ ; disallowed pcert
                                                    (null expansion-alist0)
                                                    (car expansion-alist-and-index)))
                                                  ((eq cert-op :convert-pcert)
                                                   :irrelevant) ; not used
                                                  (t
                                                   (merge-into-expansion-alist
                                                    expansion-alist0
                                                    (car expansion-alist-and-index)))))))
                                       (cond
                                        (write-acl2x
                                         (assert$
                                          (not (eq cert-op :convert-pcert))

; See the Essay on .acl2x Files (Double Certification).  Below we will exit
; certify-book-fn, so the value returned here for pass1-result will be
; ignored.

                                          (write-acl2x-file
                                           expansion-alist acl2x-file
                                           ctx state)))
                                        (t
                                         (let ((expansion-alist
                                                (cond
                                                 ((or (eq cert-op
                                                          :create-pcert)
                                                      (eq cert-op
                                                          :convert-pcert))

; The value here is irrelevant for :convert-pcert.  We avoid eliding locals for
; :create-pcert (except when pcert = t, since then we are doing just what we
; would do for ordinary certification without pcert), hence we elide along the
; way); we'll take care of that later, after dealing with pkg-names to support
; reading the unelided expansion-alist members from the .pcert0 file during the
; Convert procedure.

                                                  expansion-alist)
                                                 (t
                                                  (elide-locals-from-expansion-alist
                                                   expansion-alist
                                                   nil)))))
                                           (value ; pass1-result:
                                            (list (let ((val (global-val
                                                              'skip-proofs-seen
                                                              (w state))))
                                                    (and val

; Here we are trying to record whether there was a skip-proofs form in the
; present book or its portcullis commands, not merely on behalf of an included
; book.  The post-alist will record such information for included books, and is
; consulted by skipped-proofsp-in-post-alist.  See the comment about this
; comment in install-event.

                                                         (not (eq (car val)
                                                                  :include-book))))
                                                  portcullis-skipped-proofsp
                                                  (f-get-global 'axiomsp state)
                                                  (global-val 'ttags-seen
                                                              (w state))
                                                  (global-val
                                                   'include-book-alist-all
                                                   (w state))
                                                  expansion-alist

; The next form represents the part of the expansion-alist that needs to be
; checked for new packages, in the sense described above the call below of
; pkg-names.

                                                  (let ((index0
                                                         (cdr expansion-alist-and-index)))
                                                    (cond
                                                     ((eq cert-op :convert-pcert)

; Presumably the packages defined in the portcullis commands of the .pcert0
; file, as computed by chk-acceptable-certify-book1, are sufficient for reading
; the expansion-alist.

                                                      nil)
                                                     ((integerp index0)
                                                      (restrict-expansion-alist
                                                       index0
                                                       expansion-alist))
                                                     (t

; Index0 is essentially "infinity" -- eval-event-lst (on behalf of
; process-embedded-events) never found an extension of the known-package-alist.
; There is thus no part of expansion-alist that needs checking!

                                                      nil)))
                                                  (global-val
                                                   'translate-cert-data
                                                   (w state)))))))))))))
                         (cond
                          (write-acl2x ; early exit
                           (value acl2x-file))
                          (t
                           (let* ((pass1-known-package-alist
                                   (global-val 'known-package-alist (w state)))
                                  (skipped-proofsp
                                   (nth 0 pass1-result))
                                  (portcullis-skipped-proofsp
                                   (nth 1 pass1-result))
                                  (axiomsp (nth 2 pass1-result))
                                  (ttags-seen (nth 3 pass1-result))
                                  (new-include-book-alist-all
                                   (nth 4 pass1-result))
                                  (expansion-alist (nth 5 pass1-result))
                                  (expansion-alist-to-check
                                   (nth 6 pass1-result))
                                  (translate-cert-data
                                   (nth 7 pass1-result))
                                  (cert-annotations
                                   (list

; We set :skipped-proofsp in the certification annotations to t or nil
; according to whether there were any skipped proofs in either the
; portcullis or the body of this book (not subbooks).

                                    (cons :skipped-proofsp skipped-proofsp)

; We similarly set :axiomsp to t or nil.  As above, subbooks are not considered
; here.

                                    (cons :axiomsp axiomsp)
                                    (cons :ttags ttags-seen)))
                                  (post-alist1 (if fast-cert-p

; With fast-cert we don't roll back the world, so we might have local-include
; book commands in the world.  We punt and simply record nil here for this
; post-alist, which forces us to rely on the build system to check that the
; included books (or at least those that would be included non-locally at
; include-book time) are all certified.  Future work could perhaps sort out
; which included books are local and hence to be ignored here.

                                                   nil
                                                 new-include-book-alist-all)))
                             (er-progn
                              (chk-cert-annotations
                               cert-annotations portcullis-skipped-proofsp
                               portcullis-cmds0 full-book-string
                               suspect-book-action-alist ctx state)
                              (cond
                               ((eq cert-op :convert-pcert)
                                (er-let*
                                    ((book-hash
                                      (book-hash
                                       nil full-book-string
                                       portcullis-cmds0
                                       (access cert-obj cert-obj
                                               :expansion-alist)
                                       (access cert-obj cert-obj
                                               :cert-data)
                                       ev-lst state))
                                     (extra-entry
                                      (value
                                       (list* full-book-name
                                              user-book-name
                                              familiar-name
                                              cert-annotations
                                              book-hash))))
                                  (certify-book-finish-convert
                                   (cons extra-entry post-alist1)
                                   (access cert-obj cert-obj :post-alist)
                                   full-book-string ctx state)))
                               (t
                                (let* ((wrld-post-pass1 (w state))
                                       (rollback-pair ; nil or consp

; There is no rollback with fast-cert, hence no rollback-pair.

                                        (and (not fast-cert-p)
                                             (global-val 'cert-replay
                                                         wrld-post-pass1)))
                                       (index
                                        (assert$
                                         (listp rollback-pair)

; If cert-replay was set while processing events in the book, then index is
; positive since the call of process-embedded-events above is made with index =
; 1 and index is incremented with each event in its main subroutine,
; eval-event-lst.

                                         (and (posp (car rollback-pair))
                                              (car rollback-pair))))
                                       (port-index

; When non-nil, this is how many of portcullis-cmds0 to discard before
; re-execution after the world is rolled back into the portcullis commands.
; Thus, we will be re-executing (nthcdr port-index portcullis-cmds0).  So for
; example, if we roll back through the first command after the boot-strap
; world, then we want to start with that first command, so port-index is 0; to
; start with the second command, port-index should be 1 so that we discard only
; the first; to start with the third command, then port-index should be 2; and
; so on.

                                        (and rollback-pair
                                             (not index)

; Note that (car rollback-pair) is the negative of the
; max-absolute-command-number at the point where 'cert-replay was set.

                                             (- (- (car (car rollback-pair)))
                                                (access
                                                 command-number-baseline-info
                                                 (global-val
                                                  'command-number-baseline-info
                                                  wrld-post-pass1)
                                                 :original))))
                                       (port-non-localp
                                        (and port-index
                                             (not (cdr (car rollback-pair)))))
                                       (rollback-wrld
                                        (if rollback-pair
                                            (cdr rollback-pair)
                                          wrld1))
                                       (cert-data-pass1-saved
                                        (and

; When the variable rollback-pair is nil, we won't be including the book for
; the local incompatibility check.  Since cert-data-pass1-saved is only used
; during that include-book, we therefore won't need it either when
; rollback-pair is nil.

                                         rollback-pair
                                         (cert-data-pass1-saved
                                          (if index
                                              rollback-wrld

; In this case, where index is nil but rollback-pair is not, we know that
; port-index is non-nil -- we will roll back the world to rollback-wrld, which
; implies rolling back all events in the book and at least one portcullis
; command.  Should we include rolled-back events from the portcullis in the
; cert-data?  It seems that we could, but we aren't including other events from
; the portcullis, so that would be odd.  Those who want the use of cert-data to
; speed up include-book can restrict the portcullis commands to defpkg and
; include-book events.

                                            wrld1)
                                          wrld-post-pass1))))
                                  (fast-alist-free-cert-data-on-exit
                                   cert-data-pass1-saved
                                   (pprogn
                                    (update-useless-runes old-useless-runes
                                                          state)
                                    (print-certify-book-step-3 index
                                                               port-index
                                                               port-non-localp
                                                               state)
                                    (cond
                                     (rollback-pair
                                      (set-w 'retraction rollback-wrld state))
                                     (t state))
                                    (let ((rollback-wrld-known-package-alist
                                           (and rollback-pair ; else don't care
                                                (global-val
                                                 'known-package-alist
                                                 rollback-wrld))))
                                      (er-progn
                                       (if port-index
                                           (eval-some-portcullis-cmds
                                            port-index portcullis-cmds0 ctx
                                            state)
                                         (value nil))
                                       (pprogn
                                        #+(and gcl (not acl2-loop-only))

; In GCL, object code (from .o files) may be stored in read-only memory, which
; is not collected by sgc.  In particular, such code just loaded from
; include-book forms (during the admissibility check pass) is now garbage but
; may stay around awhile.  Ultimately one would expect GCL to do a full garbage
; collect when relocating the hole, but by then it may have allocated many
; pages unnecessarily; and pages are never deallocated.  By collecting garbage
; now, we may avoid the need to allocate many pages during this coming
; (include-book) pass of certification.

; However, it is far from clear that we are actually reclaiming the space we
; intend to reclaim.  So we may want to delete this code.  It seems to cost
; about 1/4 second per book certification for the ACL2 regression suite (as of
; 5/07).

                                        (progn
                                          (cond
                                           ((and (not *gcl-large-maxpages*)
                                                 (fboundp 'si::sgc-on)
                                                 (funcall 'si::sgc-on))
                                            (funcall 'si::sgc-on nil)
                                            (si::gbc t)
                                            (funcall 'si::sgc-on t))
                                           (t (si::gbc t)))
                                          state)
                                        (with-hcomp-bindings
                                         compile-flg

; It may seem strange to call with-hcomp-bindings here -- after all, we call
; include-book-fn below, and we may think that include-book-fn will ultimately
; call load-compiled-book, which calls with-hcomp-bindings.  However, when
; include-book-fn is called on behalf of certify-book, it avoids calling
; include-book-raw and hence avoids calling load-compiled-book; it processes
; events without first doing a load in raw Lisp.  It is up to us to bind the
; *hcomp-xxx* variables here, so that add-trip can use them as it is processing
; events on behalf of the call below of include-book-fn, where
; *inside-include-book-fn* is 'hcomp-build.

                                         (mv-let
                                           (expansion-alist pcert-info)
                                           (cond
                                            ((eq cert-op :create-pcert)
                                             (elide-locals-and-split-expansion-alist
                                              expansion-alist acl2x-expansion-alist
                                              nil nil))
                                            (t (mv expansion-alist
                                                   (if (eq cert-op
                                                           :create+convert-pcert)
                                                       :proved
                                                     nil))))
                                           (er-let* ((portcullis-wrld
                                                      (value (if port-index
                                                                 (w state)
                                                               wrld1)))
                                                     (pre-alist
                                                      (value
                                                       (cond
                                                        (fast-cert-p

; With fast-cert we don't roll back the world, so we might have local-include
; book commands in the certification world.  We punt and simply record nil here
; for the pre-alist , which forces us to rely on the build system to check that
; the included books from the portcullis commands (or at least those that would
; be included non-locally at include-book time) are all certified.  Future work
; could perhaps sort out which included books are local and hence to be ignored
; here.

                                                         nil)
                                                        (port-index
                                                         (global-val
                                                          'include-book-alist
                                                          portcullis-wrld))
                                                        (t pre-alist-wrld1))))
                                                     (portcullis-wrld-known-package-alist
                                                      (value
                                                       (global-val
                                                        'known-package-alist
                                                        portcullis-wrld)))
                                                     (defpkg-items

; We collect information on enough packages at the end of pass 1 to include
; those that would be missing if instead local events are skipped.  These
; packages may become hidden defpkgs; see new-defpkg-list below, and for a more
; thorough discussion see the Essay on Hidden Packages Added by Certify-book.

                                                       (if fast-cert-p
; We don't bother with hidden packages when fast-cert is active.
                                                           (value nil)
                                                         (defpkg-items
                                                           pass1-known-package-alist
                                                           (if rollback-pair
                                                               rollback-wrld-known-package-alist
                                                             wrld1-known-package-alist)
                                                           ctx portcullis-wrld state)))
                                                     (cltl-command-stack0
                                                      (value
                                                       (if fast-cert-p
                                                           (compress-cltl-command-stack
                                                            (global-val
                                                             'top-level-cltl-command-stack
                                                             (w state)))

; If we are not using fast-cert, then we will compute an appropriate
; cltl-command-stack later, when we need it.

                                                         nil)))
                                                     (declaim-list
                                                      (state-global-let*
                                                       ((ld-redefinition-action
                                                         nil))

; Note that we do not bind connected-book-directory before calling
; include-book-fn, because it will bind it for us.  We leave the directory set
; as it was when we parsed user-book-name to get full-book-name, so that
; include-book-fn will parse user-book-name the same way again.

                                                       (er-progn
                                                        (hcomp-build-from-state
                                                         (if fast-cert-p
                                                             cltl-command-stack0
                                                           (global-val
                                                            'top-level-cltl-command-stack
                                                            (w state)))
                                                         state)
                                                        (cond
                                                         (rollback-pair
                                                          (include-book-fn
                                                           user-book-name
                                                           state
                                                           nil
                                                           (cons
                                                            (if index ; rollback is into book
                                                                (cert-include-expansion-alist
                                                                 index
                                                                 expansion-alist)
; Else the world is rolled back into the certification world.
                                                              expansion-alist)
                                                            cert-data-pass1-saved)
                                                           uncertified-okp
                                                           defaxioms-okp
                                                           skip-proofs-okp
                                                           ttags-seen
                                                           nil
                                                           nil))
                                                         (t
                                                          (get-declaim-list
                                                           state))))))
                                                     (ignore
                                                      (cond
                                                       (rollback-pair

; There is a long comment in include-book-fn1 about not allowing
; "process-embedded-events to set the ACL2 defaults table at the end".  So if
; we are doing an include-book here, we take care of that setting explicitly,
; thus ensuring that the original acl2-defaults-table is in place after the
; include-book-fn call above.

                                                        (maybe-install-acl2-defaults-table
                                                         saved-acl2-defaults-table
                                                         state))
                                                       (t (value nil)))))
                                             (let* ((wrld2
; This is the world after include-book (if include-book was evaluated).
                                                     (w state))
                                                    (cltl-command-stack
                                                     (if fast-cert-p
                                                         cltl-command-stack0
                                                       (global-val
                                                        'top-level-cltl-command-stack
                                                        wrld2)))
                                                    (new-fns
                                                     (top-level-user-fns
                                                      cltl-command-stack
                                                      nil))
                                                    (cert-data-pass2
                                                     (cert-data-for-certificate
                                                      new-fns
                                                      translate-cert-data
                                                      wrld2))
                                                    (pkg-names

; Warning: If the following comment is modified or deleted, visit its reference
; in pkg-names.  Also see the comments at the top of :doc note-3-2 for a
; discussion of this issue, and especially, for more context see the Essay on
; Hidden Packages Added by Certify-book.

; We may need to create a (hidden) defpkg after the portcullis commands in
; order to read the certificate's expansion-alist or cert-data before
; evaluating events from the book.  As long as there have been no new defpkg
; events in pass 1 since the end of the portcullis command evaluation, there is
; no problem.  (Note that make-event-fn calls bad-lisp-objectp to check that
; the expansion is readable after evaluating the make-event call, so there is
; no additional worry about packages introduced in support of those
; expansions.)  But once we get a new package during pass 1, any subsequent
; form in the expansion-alist may need that new package to be defined in order
; for ACL2 to read the expansion-alist from the .cert file.  Here we take the
; first step towards finding (hidden) packages that need to be added for the
; expansion-alist or cert-data.

; We use expansion-alist-to-check here, which is the part of expansion-alist
; after the first event in the book that added a package during pass 1 -- no
; earlier event is of concern here.

                                                     (pkg-names
                                                      (cons expansion-alist-to-check
                                                            cert-data-pass2)
                                                      portcullis-wrld-known-package-alist))
                                                    (new-defpkg-list
; See the Essay on Hidden Packages Added by Certify-book.
                                                     (new-defpkg-list
                                                      defpkg-items
                                                      (delete-names-from-kpa
                                                       pkg-names
                                                       (global-val
                                                        'known-package-alist
                                                        wrld2))
                                                      (if rollback-pair
                                                          rollback-wrld-known-package-alist
                                                        wrld1-known-package-alist)))
                                                    (include-book-alist-wrld2
                                                     (global-val 'include-book-alist
                                                                 wrld2))
                                                    (post-alist2
                                                     (cond
                                                      (fast-cert-p

; We punt here as we do for post-alist1; see the comment on "punt" above for
; post-alist1.

                                                       nil)
                                                      (rollback-pair

; In this case, include-book-fn was evaluated above.  The following call of cdr
; removes the certification tuple stored by the include-book-fn itself.  That
; pair is guaranteed to be the car because it is the most recently added one
; (with add-to-set-equal) and we know it was not already a member of the list
; because chk-acceptable-certify-book1 checked that.  Could a file include
; itself?  It could try.  But if (include-book file) is one of the events in
; file, then the attempt to (include-book file) will cause infinite recursion
; -- because we don't put file on the list of files we've included (and hence
; recognize as redundant) until after we've completed the processing.

                                                       (cdr
                                                        include-book-alist-wrld2))
                                                      (t include-book-alist-wrld2))))
                                               (fast-alist-free-cert-data-on-exit
                                                cert-data-pass2
                                                (pprogn
                                                 (maybe-write-bookdata
                                                  full-book-string full-book-name
                                                  wrld2 ctx state)
                                                 (mv-let
                                                   (new-bad-fns all-bad-fns)
                                                   (cond
                                                    ((or fast-cert-p
                                                         (warning-disabled-p
                                                          "Guards"))
                                                     (mv nil nil))
                                                    (t
                                                     (mv (collect-ideals new-fns
                                                                         wrld2
                                                                         nil)
                                                         (collect-ideal-user-defuns
                                                          wrld2))))
                                                   (cond
                                                    ((or new-bad-fns all-bad-fns)
                                                     (print-certify-book-guards-warning
                                                      full-book-string
                                                      new-bad-fns all-bad-fns
                                                      k ctx state))
                                                    (t state)))
                                                 (er-progn
                                                  (chk-certify-book-step-3
                                                   post-alist2 post-alist1
                                                   ctx state)
                                                  (with-cbd

; This binding is for the call of compile-certified-file below, though perhaps
; there will be other uses.

                                                   directory-name
                                                   (pprogn
; Write certificate.
                                                    (print-certify-book-step-4
                                                     full-book-string
                                                     cert-op
                                                     state)
                                                    (er-let*
                                                        ((portcullis-cmds
                                                          (value
                                                           (append? portcullis-cmds0
                                                                    new-defpkg-list)))
                                                         (book-hash
                                                          (book-hash
                                                           nil
                                                           full-book-string
                                                           portcullis-cmds
                                                           expansion-alist
                                                           cert-data-pass2
                                                           ev-lst
                                                           state))
                                                         (extra-entry
                                                          (value
                                                           (list* full-book-name
                                                                  user-book-name
                                                                  familiar-name
                                                                  cert-annotations
                                                                  book-hash))))

; It is important to write the compiled file before installing the certificate
; file, since "make" dependencies look for the .cert file, whose existence
; should thus imply the existence of an intended compiled file.  However, we
; need the compiled file to have a later write date (see load-compiled-book).
; So our approach if compile-flg is true is to write the certificate file
; first, but with a temporary name, and then move it to its final name after
; compilation (if any) has completed.

                                                      (er-let*
                                                          ((temp-alist
                                                            (make-certificate-files
                                                             full-book-string
                                                             (cons portcullis-cmds
                                                                   pre-alist)
                                                             (cons extra-entry
                                                                   post-alist1)
                                                             (cons extra-entry
                                                                   post-alist2)
                                                             expansion-alist
                                                             cert-data-pass2
                                                             pcert-info
                                                             cert-op
                                                             ctx
                                                             state))
                                                           (os-compiled-file
                                                            (cond
                                                             (compile-flg
; We only use the value of compile-flg when #-acl2-loop-only.
                                                              (pprogn
                                                               (print-certify-book-step-5
                                                                full-book-string
                                                                state)
                                                               (er-progn
                                                                (write-expansion-file
                                                                 portcullis-cmds
                                                                 declaim-list
                                                                 new-fns
                                                                 cltl-command-stack
                                                                 (expansion-filename
                                                                  full-book-string)
                                                                 expansion-alist
                                                                 pkg-names
                                                                 ev-lst
                                                                 pass1-known-package-alist
                                                                 ctx state)
                                                                #-acl2-loop-only
                                                                (let* ((os-expansion-filename
                                                                        (pathname-unix-to-os
                                                                         (expansion-filename
                                                                          full-book-string)
                                                                         state))
                                                                       (os-compiled-file
                                                                        (compile-certified-file
                                                                         os-expansion-filename
                                                                         full-book-string
                                                                         state)))
                                                                  (when (not (f-get-global
                                                                              'save-expansion-file
                                                                              state))
                                                                    (delete-expansion-file
                                                                     os-expansion-filename
                                                                     full-book-string
                                                                     state))
                                                                  (value os-compiled-file)))))
                                                             (t
                                                              #-acl2-loop-only
                                                              (delete-auxiliary-book-files
                                                               full-book-string)
                                                              (value nil)))))
                                                        (er-progn
                                                         #-acl2-loop-only
                                                         (progn
; Install temporary certificate file(s).
                                                           (delete-cert-files
                                                            full-book-string)
                                                           (loop for pair in
                                                                 temp-alist
                                                                 do
                                                                 (rename-file
                                                                  (pathname-unix-to-os
                                                                   (car pair)
                                                                   state)
                                                                  (pathname-unix-to-os
                                                                   (cdr pair)
                                                                   state)))
                                                           (when
                                                               (and
                                                                os-compiled-file

; Ensure that os-compiled-file is more recent than .cert file, since rename-file
; is not guaranteed to preserve the write-date.  We first check the
; file-write-date of the .cert file, since we have found that to be almost 3
; orders of magnitude faster than touch? in CCL.

                                                                (loop with
                                                                      compile-date =
                                                                      (file-write-date
                                                                       os-compiled-file)
                                                                      for pair
                                                                      in temp-alist
                                                                      thereis
                                                                      (< compile-date
                                                                         (file-write-date$
                                                                          (cdr pair)
                                                                          state))))
                                                             (touch?
                                                              os-compiled-file
                                                              nil ctx state))
                                                           (value nil))
                                                         (pprogn
                                                          (cond
                                                           (expansion-alist0

; Note that we are not in the Convert procedure.  So we know that
; expansion-alist0 came from a .acl2x file, not a .pcert0 file.

                                                            (observation
                                                             ctx
                                                             "Used ~
                                                              expansion-alist ~
                                                              obtained from ~
                                                              file ~x0."
                                                             acl2x-file))
                                                           (t state))
                                                          (value
                                                           full-book-string)))))))))))))))))))))))))))))))))))))))))))

(defmacro warning$-cw (ctx &rest args)
  (prog2$
   (cw "~|***NOTE***: Warning$-cw is deprecated.  Use warning$-cw0 or ~
        warning$-cw1.")
   `(warning$-cw0 ,ctx nil *default-state-vars* ,@args)))

(defmacro warning$-cw0 (ctx summary state-vars &rest args)

; This differs from warning$-cw1 in that state-vars and wrld are bound here for
; the user.

  `(let ((state-vars ,state-vars)
         (wrld nil))
     (warning$-cw1 ,ctx ,summary ,@args)))

(defun memoize-table-chk (key val wrld state)

; The usual table guard mechanism provides crude error messages when there is a
; violation.  We avoid that problem by causing a hard error.  We rely on the
; fact that illegal and hard-error return nil.

; The memoize-table maps :common-lisp-compliant function symbols (to be
; memoized or unmemoized) to nil (unmemoized) or to a non-empty alist that
; stores relevant information, such as the condition (see memoize-form).  The
; guard requirement then ensures that when we call the raw Lisp version of fn,
; then since the guard for fn must hold in that case, so does the guard for
; condition-fn.  The body of condition-fn can therefore be called in raw Lisp
; on the arguments of any call of fn made in raw Lisp from the ACL2
; read-eval-print loop.  This is important because the memoized function body
; includes code from the body of condition-fn.

  (let ((ctx '(table . memoize-table))
        (str "Illegal attempt to set memoize-table:  "))
    (cond
     ((not (symbolp key))
      (mv nil (msg "~@0The first argument of memoize must be a symbol, unlike ~
                    ~x1."
                   str key)))
     ((not (symbol-alistp val))
      (mv nil (msg "~@0Function symbol ~x1 must be associated with a ~
                    symbol-alistp, unlike ~x2."
                   str key val)))
     (t
      (let* ((memoize-table (table-alist 'memoize-table wrld))
             (key-formals (getpropc key 'formals t wrld))
             (key-class (symbol-class key wrld))
             (condition (and val (cdr (assoc-eq :condition-fn val))))
             (inline (and val (cdr (assoc-eq :inline val))))
             (aokp (and val (cdr (assoc-eq :aokp val))))
             (invoke (and val (cdr (assoc-eq :invoke val))))
             (total (and val (cdr (assoc-eq :total val))))
             (msg
              (cond
               ((eq key-formals t)
                (msg "~@0~x1 is not a function symbol."
                     str key))
               ((and (or condition (cdr (assoc-eq :inline val)))

; The preceding term says that we are not profiling.  Why not replace it simply
; with condition, allowing :inline t?  Perhaps we could, but that would require
; a bit of thought since memoization with :inline t will modify recursive
; calls, and we would need to be sure that this replacement doesn't violate
; syntactic restrictions.  We can think about this if someone has reason to
; memoize with :condition nil but not :inline nil.

                     (member-eq 'state (stobjs-in key wrld)))
                (msg "~@0~x1 takes ACL2's STATE as an argument (illegal ~
                      except for profiling)."
                     str key))
               ((not (booleanp aokp))
                (msg "~@0:aokp has a non-Boolean value, ~x1."
                     str aokp))
               ((and (or condition (cdr (assoc-eq :inline val)))

; See comment above for the case of 'state.

                     (non-memoizable-stobjs (stobjs-in key wrld) wrld))
                (mv-let
                  (abs conc)
                  (filter-absstobjs (non-memoizable-stobjs (stobjs-in key wrld)
                                                           wrld)
                                    wrld nil nil)
                  (cond
                   ((null abs)
                    (msg "~@0~x1 has input stobj~#2~[ ~&2~/s ~&2, each~] ~
                          introduced with :NON-MEMOIZABLE T.  See :DOC ~
                          defstobj."
                         str key conc))
                   ((null conc)
                    (msg "~@0~x1 has input abstract stobj~#2~[ ~&2~/s ~&2, ~
                          each of~] whose corresponding foundational stobj is ~
                          non-memoizable.  See :DOC defabsstobj."
                         str key abs))
                   (t
                    (msg "~@0~x1 has input fondational stobj~#2~[ ~&2~/s ~&2, ~
                          each~] introduced as non-memoizable.  ~x1 also has ~
                          input abstract stobj~#3~[ ~&2~/s ~&3, each of~] ~
                          whose corresponding foundational stobj is ~
                          non-memoizable.  See :DOC defstobj."
                         str key conc abs)))))
               ((member-eq key *stobjs-out-invalid*)
                (msg "~@0~x1 is a primitive without a fixed output signature."
                     str key))
               ((and (or condition (cdr (assoc-eq :inline val)))

; See comment above for the case of 'state.

                     (not (all-nils (stobjs-out key wrld))))
                (let ((stobj (find-first-non-nil (stobjs-out key wrld))))
                  (msg "~@0~x1 returns a stobj, ~x2 (illegal except for ~
                        profiling)."
                       str key stobj)))
               ((member-eq key *hons-primitive-fns*)
                (msg "~@0~x1 is a HONS primitive."
                     str key))
               ((not (cltl-def-from-name key wrld))
                (msg "~@0Although ~x1 is a defined ACL2 function, its ~
                      implementation in raw Lisp is not.~@2"
                     str key
                     (let* ((st (getpropc key 'stobj-function nil wrld))
                            (ev (and st (get-event st wrld))))
                       (cond
                        ((and ev
                              (or (and (eq (car ev) 'defstobj)
                                       (member-eq :inline ev))
                                  (eq (car ev) 'defabsstobj)))
                         (msg "  Note that ~x0 was introduced with the event ~
                               ~x1, so ~x0 is ``inlined'' by making it a ~
                               macro in raw Lisp."
                              key ev))
                        (t "")))))
               ((getpropc key 'constrainedp nil wrld)

; Should we consider removing this restriction if :INVOKE has a non-nil value?
; A potential use would be to prove some io-pairs for a given constrained
; function and then provide for execution of that constrained function; see
; community book books/kestrel/utilities/use-io-pairs.lisp.  A fundamental
; issue however is that constrained functions do not have
; executable-counterpart runes, so they presumably wouldn't be executed
; directly during proofs.  They could be executed under a call of a defined
; function, however.

                (msg "~@0~x1 is constrained.  You may instead wish to memoize ~
                      a caller or to memoize its attachment (see :DOC ~
                      defattach)."
                     str key))
               ((and inline

; The test below isn't right if a built-in function with raw Lisp code has been
; promoted to logic mode after assigning state global
; 'verify-termination-on-raw-program-okp to t.  However, that assignment may
; only be done with a trust tag, and the documentation warns that doing this
; promotion could be unsound.  So we don't worry about that case here.

; Note that here we are disallowing inline memoization of apply$-lambdas.
; That's fine; we essentially do our own memoization via the cl-cache.

                     (if (eq key-class :program)
                         (member-eq key *initial-program-fns-with-raw-code*)
                       (member-eq key *initial-logic-fns-with-raw-code*)))
                (msg "~@0The built-in function symbol ~x1 has associated ~
                      raw-Lisp code, hence is illegal to memoize unless ~
                      :RECURSIVE is nil."
                     str key))
               ((let ((pair (assoc-eq :memo-table-init-size val)))
                  (and pair (not (posp (cdr pair)))))
                (msg "~@0The :memo-table-init-size must be a positive ~
                      integer, unlike ~x1."
                     str (cdr (assoc-eq :memo-table-init-size val))))
               ((memoize-table-chk-commutative-msg str key val wrld))
               ((and invoke total)
                (msg "~@0It is illegal to specify non-nil values for both the ~
                      :INVOKE and :TOTAL memoize keywords."
                     str))
               ((and invoke inline)
                (msg "~@0It is illegal to specify a non-NIL value for the ~
                      :INVOKE keyword of memoize when the :RECURSIVE keyword ~
                      (i.e., the :INLINE keyword for the memoize table) is T."
                     str))
               ((and invoke
                     (memoize-table-chk-invoke-msg key invoke str wrld state)))
               ((not (symbolp total))
                (msg "~@0The value of the :total keyword for memoize must be ~
                      a symbol, but ~x1 is not.  Presumably you are trying to ~
                      use the :total option of memoize directly, which is not ~
                      recommended.  See :DOC memoize-partial."
                     str total))
               ((and total
                     (not (cltl-def-memoize-partial key total wrld)))
                (msg "~@0Unable to find executable Common Lisp definition for ~
                      ~x1 in the table, ~x2.  Presumably you are trying to ~
                      use the :total option of memoize directly, which is not ~
                      recommended.  See :DOC memoize-partial."
                     str total 'partial-functions-table))

; The next two checks require that we do not memoize or unmemoize a function
; that is already memoized or unmemoized, respectively.  The function
; maybe-push-undo-stack relies on this check.

               ((and val (cdr (assoc-eq key memoize-table)))
                (msg "~@0Function ~x1 is already memoized."
                     str key))
               ((and (null val) (null (cdr (assoc-eq key memoize-table))))
                (msg "~@0Cannot unmemoize function ~x1 because it is not ~
                      currently memoized."
                     str key))
               ((and (eq key-class :ideal)
                     val ; memoize, not unmemoize
                     (let* ((pair (assoc-eq :ideal-okp val))
                            (okp
                             (if pair
                                 (cdr pair)
                               (cdr (assoc-eq :memoize-ideal-okp
                                              (table-alist 'acl2-defaults-table
                                                           wrld))))))
                       (cond ((eq okp t)
                              nil)
                             ((not okp)
                              (msg "~@0The function symbol ~x1 is in :logic ~
                                    mode but has not had its guards verified. ~
                                    ~ Either run ~x2, or specify :IDEAL-OKP ~
                                    ~x3 in your ~x4 call, or else evaluate ~
                                    ~x5 or ~x6."
                                   str key 'verify-guards t 'memoize
                                   '(table acl2-defaults-table :memoize-ideal-okp
                                           t)
                                   '(table acl2-defaults-table :memoize-ideal-okp
                                           :warn)))
                             (t ; okp is :warn
                              (prog2$ (warning$-cw0
                                       'memoize-table-chk
                                       "Memoize"
                                       (default-state-vars t)
                                       "The function ~x0 to be memoized is in ~
                                        :logic mode but has not had its ~
                                        guards verified.  Memoization might ~
                                        therefore not take place; see :DOC ~
                                        memoize."
                                       key)
                                      nil))))))

; Finally, check conditions on the memoization condition function.

               (t
                (let ((val-formals (and condition
                                        (if (symbolp condition)
                                            (getpropc condition 'formals t wrld)
                                          t)))
                      (val-guard (and condition
                                      (if (symbolp condition)
                                          (getpropc condition 'guard *t* wrld)
                                        t))))

                  (cond
                   ((or (eq val nil)
                        (member-eq condition '(t nil)))
                    nil)
                   ((eq val-formals t)
                    (msg "~@0The proposed memoization condition function, ~
                          ~x1, is neither T, NIL, nor a function symbol known ~
                          to ACL2."
                         str condition))
                   ((not (and (symbolp condition)
                              (or (eq key-class :program)
                                  (eq (symbol-class condition wrld)
                                      :common-lisp-compliant))))
                    (msg "~@0Function ~x1 cannot serve as a memoization ~
                          condition function for function ~x2, because unlike ~
                          ~x2, ~x1 is not common-lisp-compliant (a logic-mode ~
                          function that has had its guards verified)."
                         str condition key))
                   ((not (equal key-formals val-formals))
                    (msg "~@0Function ~x1 cannot serve as a memoization ~
                          condition function for ~x2, because the two ~
                          functions have different formal parameter lists."
                         str condition key))
                   ((not (equal (getpropc key 'guard *t* wrld)
                                val-guard))
                    (msg "~@0Function ~x1 cannot serve as a memoization ~
                          condition function for ~x2, because the two ~
                          functions have different guards."
                         str condition key))
                   (t nil)))))))
        (progn$
         (and val
              (let ((stobjs-in (stobjs-in key wrld)))
                (cond
                 ((and condition
                       (find-first-non-nil stobjs-in))
                  (let ((input-stobjs (collect-non-x nil stobjs-in)))
                    (observation-cw
                     ctx
                     "The function ~x0 has input stobj~#1~[~/s~] ~&1.  The ~
                      memoization table for ~x0 will be cleared whenever ~
                      ~#2~[this stobj is~/either of these stobjs is~/any of ~
                      these stobjs is~] updated.  Any update of a stobj may ~
                      therefore be significantly slower, perhaps by a factor ~
                      of 5 or 10, when it is an input of a memoized function."
                     key
                     input-stobjs
                     (zero-one-or-more (cdr input-stobjs)))))
                 (t nil))))
         (if msg
             (mv nil msg)
           (mv t nil))))))))

;;; Comment change only.
(defmacro warning$ (ctx summary str+ &rest fmt-args)

; Warning: Keep this in sync with warning$-cw1.

; Note: This macro was originally defined in basis-a.lisp, but was moved
; forward after *acl2-files* was changed so that "hons-raw" occurs before
; "basis-a".

; A typical use of this macro might be:
; (warning$ ctx "Loops" "The :REWRITE rule ~x0 loops forever." name) or
; (warning$ ctx nil "The :REWRITE rule ~x0 loops forever." name).
; If the second argument is wrapped in a one-element list, as in
; (warning$ ctx ("Loops") "The :REWRITE rule ~x0 loops forever." name),
; then no check will be made for whether the warning is disabled, presumably
; because we are in a context where we know the warning is enabled.

  (list 'warning1
        ctx

; We seem to have seen a GCL 2.6.7 compiler bug, laying down bogus calls of
; load-time-value, when replacing (consp (cadr args)) with (and (consp (cadr
; args)) (stringp (car (cadr args)))).  But it seems fine to have the semantics
; of warning$ be that conses are quoted in the second argument position.

        (if (consp summary)
            (kwote summary)
          summary)
        str+
        (make-fmt-bindings *base-10-chars* fmt-args)
        'state))

(defconst *protected-system-state-globals*
  (let ((val
         (set-difference-eq
          (union-eq (strip-cars *initial-ld-special-bindings*)
                    (strip-cars *initial-global-table*))
          '(acl2-raw-mode-p ;;; keep raw mode status
            bddnotes        ;;; for feedback after expansion failure

; We handle world and enabled structure installation ourselves, with set-w! and
; revert-world-on-error.  We do not want to rely just on state globals because
; the world protection/modification functions do pretty fancy things.

            current-acl2-world global-enabled-structure
            acl2-world-alist           ;;; manage this ourselves, e.g., for pso
            inhibit-output-lst         ;;; allow user to modify this in a book
            inhibited-summary-types    ;;; allow user to modify this in a book
            keep-tmp-files             ;;; allow user to modify this in a book
            make-event-debug           ;;; allow user to modify this in a book
            saved-output-token-lst     ;;; allow user to modify this in a book
            print-clause-ids           ;;; allow user to modify this in a book
            fmt-soft-right-margin      ;;; allow user to modify this in a book
            fmt-hard-right-margin      ;;; allow user to modify this in a book
            compiler-enabled           ;;; allow user to modify this in a book
            port-file-enabled          ;;; allow user to modify this in a book
            parallel-execution-enabled ;;; allow user to modify this in a book
            waterfall-parallelism      ;;; allow user to modify this in a book
            warnings-as-errors         ;;; allow user to modify this in a book
            waterfall-parallelism-timing-threshold ;;; see just above
            waterfall-printing ;;; allow user to modify this in a book
            waterfall-printing-when-finished ;;; see just above
            saved-output-reversed ;;; for feedback after expansion failure
            saved-output-p        ;;; for feedback after expansion failure
            ttags-allowed         ;;; propagate changes outside expansion
            ld-evisc-tuple        ;;; see just above
            term-evisc-tuple      ;;; see just above
            abbrev-evisc-tuple    ;;; see just above
            gag-mode-evisc-tuple  ;;; see just above
            slow-array-action     ;;; see just above
            iprint-ar             ;;; see just above
            iprint-fal            ;;; see just above
            iprint-soft-bound     ;;; see just above
            iprint-hard-bound     ;;; see just above
            trace-co              ;;; see just above
            trace-specs           ;;; see just above
            giant-lambda-object   ;;; see just above
            show-custom-keyword-hint-expansion
            timer-alist                ;;; preserve accumulated summary info
            main-timer                 ;;; preserve accumulated summary info
            verbose-theory-warning     ;;; warn if disabling a *bbody-alist* key
            pc-ss-alist                ;;; for saves under :instructions hints
            last-step-limit            ;;; propagate step-limit past expansion
            illegal-to-certify-message ;;; needs to persist past expansion
            splitter-output            ;;; allow user to modify this in a book
            serialize-character        ;;; allow user to modify this in a book
            serialize-character-system ;;; ditto; useful during certification
            top-level-errorp           ;;; allow TOP-LEVEL errors to propagate

; Do not remove deferred-ttag-notes or deferred-ttag-notes-saved from this
; list!  Consider the following example.

;   (make-event (er-progn (set-deferred-ttag-notes t state)
;                         (defttag t1)
;                         (defttag t2)
;                         (value '(value-triple :done))))

; When deferred-ttag-notes and deferred-ttag-notes-saved were not in this list
; (through Version_7.1), we never saw a TTAG NOTE for :T2.

            deferred-ttag-notes       ;;; see comment immediately above
            deferred-ttag-notes-saved ;;; see comment immediately above

            useless-runes             ;;; need changes from with-useless-runes

            fast-cert-status          ;;; illegal to set during make-event
                                      ;;; expansion, so no need to protect it

; The following two are protected a different way; see
; protect-system-state-globals.

            writes-okp
            cert-data
            gag-state-saved
            ))))
    val))

;;; Mods for books/std/util/add-io-pairs.lisp

(defun get-io-pairs-fn (fns wrld warnp state)

; To see how this works, see the comment in get-io-pairs-fn2 and try running
; get-io-pairs after evaluating the following.

; (trace$ get-io-pairs-fn2 get-io-pairs-fn2-lst get-io-pairs-fn1)

  (b* ((tbl (table-alist 'io-pairs-table wrld))
       (tbl-fns (strip-cars tbl))
       (allp (equal fns '(:all)))
       (bad (and (not allp)
                 (set-difference-eq fns tbl-fns)))
       (fns (cond (allp tbl-fns)
                  (bad (intersection-eq fns tbl-fns))
                  (t fns)))
       (- (and bad
               warnp
               (warning$-cw0 'get-io-pairs
                             nil
                             (default-state-vars t)
                             "There ~#0~[is no I/O pair for the symbol~/are ~
                              no I/O pairs for the symbols~] ~&0."
                             bad))))
    (get-io-pairs-fn1 fns tbl wrld)))

(defmacro get-io-pairs (&rest fns)
  (declare (xargs :guard (symbol-listp fns)))
  (if (and (member-eq :all fns)
           (not (equal fns '(:all))))
      '(er soft 'get-io-pairs
           "It is illegal to use :ALL with ~x0 except in the form ~x1."
           'get-io-pairs
           '(get-io-pairs :all))
    `(get-io-pairs-fn ',fns (w state) t state)))

(defun show-io-pairs-fn (fns state)
  (b* (((when (and (member-eq :all fns)
                   (not (equal fns '(:all)))))
        (er soft 'show-io-pairs
            "It is illegal to use :ALL with ~x0 except in the form ~x1."
            'show-io-pairs
            '(show-io-pairs :all)))
       (wrld (w state))
       (chan (standard-co state))
       (allp (equal fns '(:all)))
       (pairs (get-io-pairs-fn (or fns '(:all)) wrld nil state)))
    (pprogn
     (cond
      ((null pairs)
       (fms "There are no verified I/O pairs to display~#0~[~/ for the symbol ~
             ~v1~/ for any of the symbols ~v1~].~|"
            (list (cons #\0 (zero-one-or-more (and (not allp) fns)))
                  (cons #\1 (and (not allp) fns)))
            chan state nil))
      (t (pprogn (fms "Verified I/O pairs ((fn arg1 .. argn) result):~|"
                      nil chan state nil)
                 (show-io-pairs-lst pairs chan wrld state))))
     (value :invisible))))

;;; In books/kestrel/utilities/magic-macroexpand1-dollar.lisp,
;;; added warnings-as-errors and inhibit-output-lst to the list is lemma
;;; bound-global1-when-state-p1.

;;; For :DOC note-8-6:

"

 <p>Added utility @(tsee set-warnings-as-errors), which can change @(see
 warnings) to hard @(see errors).  Thanks to Mark Greenstreet for the idea and
 for discussions that were helpful in refining it.</p>

"

"

 <p>The behavior of @(tsee pso) and related utilities (@(tsee pso!), @(tsee
 psof), and @(tsee psog)) has been modified to avoid introducing warnings that
 were not originally printed.  For example, the output generated by @(':pso')
 below no longer prints the warning that had been suppressed for the
 @('defthm') event below.</p>

 @({
 (set-inhibit-output-lst '(warning proof-tree))
 (defthm foo t
   :hints ((\"Goal\" :use car-cons))
   :rule-classes nil)
 :pso
 })

 <p>The above change has additional, small output effects, probably for the
 better.  For example, output from the form @('(with-output :off (error
 summary) (thm (equal x y)))') no longer prints the line shown below (at the
 end).</p>

 @({
 ACL2 Error [Failure] in ( THM ...):  See :DOC failure.
 })

"

(defxdoc set-inhibit-er
  :parents (output-controls errors)
  :short "Control the error output"
  :long "@({
  Examples:
  (set-inhibit-er \"translate\" \"failure\")
 })

 <p>Note: This is an event!  It does not print the usual event @(see summary)
 but nevertheless changes the ACL2 logical @(see world) and is so recorded.  It
 is @(tsee local) to the book or @(tsee encapsulate) form in which it occurs;
 see @(see set-inhibit-er!) for a corresponding non-@(tsee local) event.
 Indeed, @('(set-inhibit-er ...)') is equivalent to @('(local
 (set-inhibit-er! ...))').</p>

 @({
  General Form:
  (set-inhibit-er string1 string2 ...)
 })

 <p>where each string is considered without regard to case.  This macro is is
 essentially @('(local (table inhibit-er-table nil 'alist :clear))'),
 where @('alist') pairs each supplied string with @('nil'): that is, @('alist')
 is @('(pairlis$ lst nil)') where @('lst') is the list of strings supplied.
 This macro is an event (see @(see table)), but no output results from a
 @('set-inhibit-er') event.</p>

 <p>ACL2 prints errors that are generally important to see.  This utility is
 appropriate for situations where one prefers not to see all error messages.
 Individual ``labeled'' error output can be silenced, but note that the error
 will still be signaled when silenced; it will just occur without printing the
 usual message.</p>

 <p>Consider for example</p>

 @({
  ACL2 Error [Failure] in ( DEFUN FOO ...):  See :DOC failure.
 })

 <p>Here, the label is \"Failure\".  The argument list for
 @('set-inhibit-er') is a list of such labels, each of which is a string.
 Any error message is suppressed if its label is a member of this list, where
 case is ignored.  Thus, for example, the error output above will be avoided
 after a call of @('set-inhibit-er') that contains the string,
 @('\"Failure\"') (or any string that is @(tsee string-equal) to
 @('\"Failure\"'), such as @('\"failure\"') or @('\"FAILURE\"')).  In summary:
 the effect of this event is to suppress any error output whose label is a
 member of the given argument list, where case is ignored.</p>

 <p>At this time, many error messages are printed without a label, for example
 (as of this writing) the following.</p>

 @({
 ACL2 !>(+ x 3)


 ACL2 Error in TOP-LEVEL:  Global variables, such as X, are not allowed.
 See :DOC ASSIGN and :DOC @.

 ACL2 !>
 })

 <p>These can only be suppressed by turning off all error output; see @(see
 set-inhibit-output-lst).  Feel free to ask the ACL2 implementors to add
 labels; for example, you might ask for a label in the example above (which
 could be @('\"Globals\"') or @('\"Global-variables\"')).</p>

 <p>Note that @('set-inhibit-er') has no effect on the value(s) returned by an
 expression (excepting the ACL2 @(see state) since it formally includes
 output).</p>

 <p>The list of currently inhibited error types is the list of keys in the
 @(see table) named @('inhibit-er-table').  (The values in the table are
 irrelevant.)  One way to get that value is to get the result from evaluating
 the following form: @('(table-alist 'inhibit-er-table (w state))').  Of
 course, if error output is inhibited overall &mdash; see @(see
 set-inhibit-output-lst) &mdash; then this value is entirely irrelevant.</p>

 <p>See @(tsee toggle-inhibit-er) for a way to add or remove a single
 string.</p>")

(defxdoc warnings
  :parents (output-controls)
  :short "Warnings emitted by the ACL2 proof process"
  :long "<p>The prover can emit many warnings when processing @(see events).
 See @(see set-inhibit-warnings) and see @(see set-inhibit-output-lst) for how
 to disable and enable them.  See also @(tsee toggle-inhibit-warning) and
 @(tsee set-warnings-as-errors).</p>")

(defxdoc set-warnings-as-errors
  :parents (warnings errors output-controls)
  :short "Changing @(see warnings) to hard @(see errors) (and vice-versa)"
  :long "<p>It is common for ACL2 users not to notice warnings.  That problem
 can be avoided by using the utility @('set-warnings-as-errors') to convert
 warnings to errors.  We start below with a general specification, followed by
 examples forms, and concluding with an extended example.</p>

 <h3>General Form</h3>

 <p>The general form is</p>

 @({
 (set-warnings-as-errors flg types state)
 })

 <p>where @('flg') is @('t'), @(':always'), or @('nil') and @('types') is
 either @(':all') or a list of strings.  The effect is to turn certain @(see
 warnings) into hard @(see errors), aborting the computation in progress.  Note
 that @('set-warnings-as-errors') is a function, so all arguments are
 evaluated.  The warnings thus affected are determined as follows.</p>

 <ul>

 <li>No warning whose type specified by constant
 @('*uninhibited-warning-summaries*') is converted to an error.  Those types
 are the ones that belong, with a case-insensitive check, to the list
 @(`*uninhibited-warning-summaries*`).  This exception overrides all discussion
 below.</li>

 <li>The behavior of @(see warnings) is affected for every warning type
 specified by the @('types') argument.  When its value is @(':all'), then all
 warnings are affected.  Otherwise the value of @('types') is a list of warning
 types (see @(see set-inhibit-warnings)): a true list of strings, each treated
 as case-insensitive.  Note that when the value is not @(':all'), the existing
 behavior for warning types is only changed for those in the value of
 @('types').</li>

 <li>When @('flg') is @(':always'), then every warning specified by @('types')
 is converted to a hard error, which aborts the evaluation in progress.  This
 happens even if the warning is suppressed (by @(tsee set-inhibit-output-lst)
 or @(tsee set-inhibit-warnings)).</li>

 <li>When @('flg') is @('t'), then when a warning specified by @('types') is to
 be printed, it is converted to a hard error, which aborts the evaluation in
 progress.  There is no error, however, if the warning is suppressed.</li>

 <li>When @('flg') is @('nil'), then every warning specified by @('types') is
 treated as a warning even if it had previously been treated as an error.</li>

 <li>When a warning of a given type (possibly @('nil') type) is converted to a
 hard error as specified above, then whether that error is printed is
 controlled by the usual mechanism for suppressing error messages; see @(see
 set-inhibit-er).  Note that the error will still be signaled regardless of
 whether the error message is thus suppressed.</li>

 <li>Previous evaluations of calls of @('set-warnings-as-errors') are ignored
 during @(tsee certify-book) and @(tsee include-book).  The handling of
 warnings as errors is restored at the end of these operations to what it was
 at the beginning.</li>

 </ul>

 <h3>Example Forms</h3>

 @({
 ; When a [Subsume] or [Use] warning is to be printed, cause a hard error
 ; instead with a similar message.
 (set-warnings-as-errors t '(\"Subsume\" \"Use\") state)

 ; As above, but cause a hard error even if the warning is not to be printed,
 ; i.e., even if by default it would be suppressed as a warning because of
 ; prior use of set-inhibit-output-lst or set-inhibit-warnings.
 (set-warnings-as-errors :always '(\"Subsume\" \"Use\") state)

 ; Restore the treatment of [Use] warnings as warnings.
 (set-warnings-as-errors nil '(\"Use\") state)

 ; Treat a warning as a hard error, but only if the warning is to be printed
 ; (hence not suppressed by set-inhibit-output-lst or set-inhibit-warnings).
 (set-warnings-as-errors t :all state)

 ; Treat a warning as a hard error, whether the warning is printed or not.
 (set-warnings-as-errors :always :all state)

 ; Restore the default behavior, treating warnings as warnings, not errors.
 (set-warnings-as-errors nil :all state)
 })

 <h3>Extended Example</h3>

 <p>ACL2 often prints @(see warnings), often with a message that includes a
 warning type.  Here is a contrived example.</p>

 @({
 (defthm foo t
  :hints ((\"Goal\" :use car-cons))
  :rule-classes nil)
 })

 @({
 ACL2 Warning [Use] in ( DEFTHM FOO ...):  It is unusual to :USE the
 formula of an enabled :REWRITE or :DEFINITION rule, so you may want
 to consider disabling (:REWRITE CAR-CONS) in the hint provided for
 Goal.  See :DOC using-enabled-rules.
 })

 <p>In the example above, the warning type is the string, @('\"Use\'') which is
 treated as case-insensitive; see @(see set-inhibit-warnings).  But maybe we
 prefer that every such warning be converted to an error; after all, as the
 warning suggests, we might want to disable the used rule first.  It's easy to
 miss a warning but not an error, so we might do the following.</p>

 @({
 (set-warnings-as-errors t '(\"use\") state)
 })

 <p>That modifies ACL2 behavior such that instead of the warning above, we get
 the following error (after using @(':u') to undo the effects of the
 @('defthm') event above).</p>

 @({
 HARD ACL2 ERROR [Use] in ( DEFTHM FOO ...):  It is unusual to :USE
 the formula of an enabled :REWRITE or :DEFINITION rule, so you may
 want to consider disabling (:REWRITE CAR-CONS) in the hint provided
 for Goal.  See :DOC using-enabled-rules.
 })

 <p>Note that this is a &ldquo;hard&rdquo; error: it aborts the computation in
 progress.</p>

 <p>Suppose however that we turn off the warning by evaluating either of the
 following two forms.</p>

 @({
 (set-inhibit-output-lst '(warning proof-tree))
 ; OR
 (set-inhibit-warnings \"use\")
 })

 <p>After evaluating either (or both) of these forms, the @('defthm') form
 above completes with no warnings or errors.  That's because there was no
 warning to print, and the @('flg') value of @('t') only has an effect for
 warnings that are printed.  If we want errors to occur even for warnings whose
 printing is suppressed, we should use the @('flg') value, @(':always').</p>

 @({
 (set-warnings-as-errors :always '(\"use\") state)
 ; OR
 (set-warnings-as-errors :always :all state)
 })")

#|
~/acl2/temp2$ diff /Users/kaufmann/acl2/temp2/books/demos/defabsstobj-example-4-log.out /Users/kaufmann/acl2/temp2/books/demos/defabsstobj-example-4-log.txt
551a552,553
> ACL2 Error [Failure] in ( THM ...):  See :DOC failure.
>
~/acl2/temp2$ mv /Users/kaufmann/acl2/temp2/books/demos/defabsstobj-example-4-log.out /Users/kaufmann/acl2/temp2/books/demos/defabsstobj-example-4-log.txt
~/acl2/temp2$
|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; The file tmp.msg used for the command
;;;   git commit -a -F tmp.msg
;;; is shown below (not part of the original patch file).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
Added utility set-warnings-as-errors to turn warnings into errors.  Tweaked output production, in particular from :pso.  Deprecated warning$-cw, replacing it with new utility warning$-cw0.  Fixed guard for warning1-cw.  Improved :DOC set-inhibit-er.

Quoting :DOC note-8-6:

  Added utility [set-warnings-as-errors], which can change [warnings]
  to hard [errors].  Thanks to Mark Greenstreet for the idea and for
  discussions that were helpful in refining it.

  The behavior of [pso] and related utilities ([pso!], [psof], and
  [psog]) has been modified to avoid introducing warnings that were
  not originally printed.  For example, the output generated by :pso
  below no longer prints the warning that had been suppressed for the
  defthm event below.

    (set-inhibit-output-lst '(warning proof-tree))
    (defthm foo t
      :hints (("Goal" :use car-cons))
      :rule-classes nil)
    :pso

  The above change has additional, small output effects, probably for
  the better.  For example, output from the form (with-output :off
  (error summary) (thm (equal x y))) no longer prints the line shown
  below (at the end).

    ACL2 Error [Failure] in ( THM ...):  See :DOC failure.

Quoting comments in (defxdoc note-8-6 ...):

; Deprecated warning$-cw in place of new utility, warning$-cw0.

; Fixed guard for warning1-cw (warning$, ...?) to allow summary of ("foo").

Clarified in :DOC set-inhibit-er that when this utility silences an
error's output, it does not stop the error from being signaled.

Passed "make devel-check" and "make proofs" in addition to the usual
"make regression-everything".
|#
