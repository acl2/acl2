; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(include-book "kestrel/utilities/tables" :dir :system)

(defun extend-prover-error-output-off (string-alist state)
  (declare (xargs :mode :program :stobjs state))
  (let ((alist (union-equal string-alist
                            (table-alist 'inhibit-er-table (w state)))))
    (with-output!
      :off (event summary)

; The following is based on (table inhibit-er-table nil alist :clear).

      (table-fn 'inhibit-er-table
                `(nil ',alist :clear)
                state
                `(table inhibit-er-table nil ',alist :clear)))))

(defun formal-quote-args (lst)
  (declare (xargs :mode :logic :guard (true-listp lst)))
  (cond ((endp lst) nil)
        ((eq (car lst) 'state)
         (cons ''state
               (formal-quote-args (cdr lst))))
        (t (cons `(list 'quote ,(car lst))
                 (formal-quote-args (cdr lst))))))

(defmacro catch-hard-error (flg form)

; Form should be a call of a function symbol or a "function-like" macro name.
; Returns the error triple produced by form, except that if flg is true, then
; we get an error triple suitably based on the trans-eval of an appropriate
; form.

  `(if ,flg
       (er-progn
        (extend-prover-error-output-off '(("Call depth") ("Evaluation"))
                                        state)
        (mv-let (erp stobjs-out/replaced-val state)
          (trans-eval-no-warning
           (list ',(car form) ,@(formal-quote-args (cdr form)))
           'prove$ state t)
          (mv (or erp
                  (car (cdr stobjs-out/replaced-val)))
              (cadr (cdr stobjs-out/replaced-val))
              state)))
     ,form))

(defun prove$-fn (term state hints instructions otf-flg ignore-ok skip-proofs
                       prover-error-output-off catch-hard-error)

; This function is based on thm-fn and defthm-fn1.  It returns (value t) if the
; proof succeeds, else (value nil).  It returns a soft error if there is a
; translation failure.

  (declare (xargs :mode :program :stobjs state))
  (revert-world
   (let ((ctx "( PROVE$ ...)"))
     (state-global-let*
      ((abort-soft nil) ; interrupts abort immediately to the top level
       (ld-skip-proofsp (if (eq skip-proofs :same)
                            (ld-skip-proofsp state)
                          skip-proofs)))
      (er-let* ((wrld0 (value (w state)))
                (wrld1 (value (table-programmatic
                               'acl2-defaults-table
                               :ignore-ok ignore-ok wrld0)))
                (tterm (translate term t t t ctx wrld1 state))
                (instructions
                 (cond ((null instructions) (value nil))
                       (hints (er soft ctx
                                  "It is illegal to supply non-nil values for ~
                                  both :hints and :instructions to ~x0."
                                  'prove$))
                       (t (translate-instructions nil instructions ctx wrld1
                                                  state))))
                (thints (translate-hints+ 'thm
                                          hints
                                          (and (null instructions)
                                               (default-hints wrld0))
                                          ctx wrld1 state)))
        (er-progn
         (extend-prover-error-output-off
          (cond ((eq prover-error-output-off t)
; "Call depth" and  "Evaluation" are dealt with above the trans-eval call.
                 '(("Failure")
                   ("Step-limit")))
                ((string-listp prover-error-output-off)
                 (pairlis$ prover-error-output-off nil))
                (t (er hard ctx
                       "Illegal value for :prover-error-output-off argument, ~
                       ~x0 (value must be t or a list of strings)"
                       prover-error-output-off)))
          state)
         (mv-let (erp val state)
           (with-ctx-summarized
            ctx
            (cond
             (instructions
              (catch-hard-error
               catch-hard-error
               (proof-builder nil tterm term nil instructions
                              (w state) state)))
             (t (let ((ens (ens state)))
                  (catch-hard-error
                   catch-hard-error
                   (prove tterm
                          (make-pspv ens (w state) state
                                     :displayed-goal term
                                     :otf-flg otf-flg)
                          thints ens (w state) ctx state))))))
           (declare (ignore val))
           (value (null erp)))))))))

(defun make-with-prover-time-limit (time form)
  `(let ((with-prover-time-limit+-var ,time)) ; avoid duplicate evaluation
     (if with-prover-time-limit+-var
         (with-prover-time-limit with-prover-time-limit+-var
                                 (check-vars-not-free
                                  (with-prover-time-limit+-var)
                                  ,form))
       ,form)))

(defun prove$-macro-fn (term hints instructions otf-flg with-output time-limit
                             step-limit ignore-ok skip-proofs
                             prover-error-output-off catch-hard-error)
  (declare (xargs :mode :program))
  (let* ((form `(prove$-fn ,term state ,hints ,instructions ,otf-flg ,ignore-ok
                           ,skip-proofs ,prover-error-output-off
                           ,catch-hard-error))
         (form `(with-output! ,@with-output ,form))
         (form (if time-limit
                   (make-with-prover-time-limit time-limit form)
                 form))
         (form (if step-limit

; The following handling of the step-limit may be surprising.  It would be
; natural to impose with-prover-time-limit! inside prove$-fn, but then the
; subsequent value returned by (last-prover-steps state) fails to be negative
; when the step-limit is exceeded, contradicting its specification.  The
; failure is due to the way with-ctx-summarized handles step-limits.  So we
; place with-prover-step-limit! on the outside of with-ctx-summarized, hence on
; the outside of prove$-fn, with the consequence that we convert a soft error
; to (value nil) below, as expected, by checking whether the step-limit has
; been exceeded.

                   `(mv-let (erp val state)
                      (with-prover-step-limit! ,step-limit ,form)
                      (let ((steps (last-prover-steps state)))
                        (if (and steps (< steps 0))
                            (value nil)
                          (mv erp val state))))
                 form)))
    form))

(defmacro prove$ (term &key
                       hints instructions otf-flg
                       (with-output '(:off :all :on error :gag-mode nil))
                       time-limit
                       step-limit
                       (ignore-ok 't)
                       (skip-proofs ':same)
                       (prover-error-output-off 't)
		       (catch-hard-error 't))

; All of the arguments except :with-output and catch-hard-error are evaluated.
; The result is (mv nil t state) if the proof is successful, otherwise (mv nil
; nil state).

  (declare (xargs :guard (member-eq ignore-ok '(t nil :warn))))
  (prove$-macro-fn term hints instructions otf-flg with-output time-limit
                   step-limit ignore-ok skip-proofs
                   prover-error-output-off catch-hard-error))

(set-guard-msg prove$
               (msg "Illegal value for :IGNORE-OK keyword of ~x0: ~x1.  The ~
                     legal values are ~&2."
                    'prove$
                    (cadr (assoc-keyword :ignore-ok (cdr args)))
                    '(t nil :warn)))

(defxdoc prove$
  :parents (kestrel-utilities system-utilities-non-built-in)
  :short "A way to call the prover from a program"
  :long "<p>For examples, see community book
 @('books/tools/prove-dollar-tests.lisp').</p>

 @({
 General Form:
 (prove$ term                    ; any term (translated or not)
         &key
         hints                   ; default nil
         ignore-ok               ; default t
         instructions            ; default nil
         otf-flg                 ; default nil
         prover-error-output-off ; default t
         skip-proofs             ; default :same
         step-limit              ; default nil
         time-limit              ; default nil
         with-output)            ; default (:off :all :on error :gag-mode nil)
 })

 <p>where all arguments except @('with-output') are evaluated.  The value of
 keyword @(':with-output'), if supplied, should be a list containing arguments
 one would give to the macro, @(tsee with-output), hence a list that satisfies
 @(tsee keyword-value-listp).  The @(tsee hints), @(tsee instructions), @(tsee
 otf-flg), @(tsee time-limit), and @(tsee step-limit) arguments are as one
 would expect for calls of the prover; see @(see defthm).  It is illegal to
 supply non-@('nil') values for both @('hints') and @('instructions').  The
 @('ignore-ok') option has the same effect as if @(see set-ignore-ok) were
 called with that same value, immediately preceding the call of @('prove$')
 &mdash; but of course warning and error messages may be suppressed, depending
 on @('with-output').  The @('skip-proofs') option defaults to @(':same'),
 which causes @('prove$') to avoid proofs during @(tsee include-book) and, more
 generally, any time that @('(ld-skip-proofsp state)') is not @('nil').  When
 @('skip-proofs') is not @(':same') then proofs take place if and only if the
 value of @('skip-proofs') is not @('nil'), as though @('(set-ld-skip-proofsp
 state)') were evaluated immediately preceding evaluation of the @('prove$')
 call.  Finally, the value of @('prover-error-output-off') must be either
 @('t'), which represents the list @('(\"Failure\" \"Step-limit\")'), or a list
 of strings; error messages arising during the proof whose type is one of these
 strings is to be suppressed, as though @(tsee set-inhibit-er) had been
 executed on these strings.</p>

 <p>@('Prove$') returns an @(see error-triple), @('(mv erp val state)').  If
 there is a syntax error (so-called ``translation error'') in the given term,
 hints, or instructions, then @('erp') is non-@('nil').  Otherwise, @('erp') is
 @('nil') and @('val') is @('t') when term is successfully proved, else
 @('nil').</p>

 <p>Note that after evaluation of a @('prove$') call, you can evaluate the form
 @('(last-prover-steps state)') to get the number of prover steps that were
 taken &mdash; except, a negative number indicates a step-limit violation.  See
 @(See last-prover-steps).</p>")

