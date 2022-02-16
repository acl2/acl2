; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defmacro with-error-output? (flg form)
  `(if ,flg
       (with-output! :on error ,form)
     ,form))

(defun prove$-fn (term state hints instructions otf-flg ignore-ok ignore-ok-p
                       with-translate-error)

; This function is based on thm-fn.  It returns (value t) if the proof
; succeeds, else (value nil).

; The step-limit mechanism is tricky, and seems to be responsible for allowing
; this function to return (mv t nil state), which surprises me.

  (declare (xargs :mode :program :stobjs state))
  (with-ctx-summarized
   "( PROVE$ ...)"
   (let ((wrld (w state))
         (ens (ens state)))
     (mv-let (erp val state)
       (with-error-output?
        with-translate-error
        (er-let* ((wrld
                   (value (cond ((null ignore-ok-p) wrld)
                                (t (putprop 'acl2-defaults-table
                                            'table-alist
                                            (acons :ignore-ok
                                                   ignore-ok
                                                   (table-alist
                                                    'acl2-defaults-table
                                                    (w state)))
                                            wrld)))))
                  (hints (translate-hints+ 'thm
                                           hints
                                           (default-hints wrld)
                                           ctx wrld state))
                  (instructions
                   (cond ((and hints instructions)
                          (er soft ctx
                              "It is illegal to supply non-nil values for ~
                               both :hints and :instructions."))
                         (t (translate-instructions nil instructions ctx wrld
                                                    state))))
                  (tterm (translate term t t t ctx wrld state)))
          (value (list* hints instructions tterm))))
       (cond
        ((and erp with-translate-error)
         (mv :translate-error :translate-error state))
        (t
         (state-global-let*
          ((abort-soft nil)) ; interrupts abort immediately to the top level
          (let ((hints (car val))
                (instructions (cadr val))
                (tterm (cddr val)))
            (cond
             (instructions
              (er-progn
               (pc-main tterm term nil nil instructions '(exit) t t state)
               (if (goals) (silent-error state) (value :success))))
             (t
              (prove tterm
                     (make-pspv ens wrld state
                                :displayed-goal term
                                :otf-flg otf-flg)
                     hints ens wrld ctx state)))))))))))

(defmacro prove$-return (form)
  `(mv-let (erp val state)
     ,form
     (cond ((and (eq erp :translate-error)
                 (eq val :translate-error))
            (silent-error state))
           (erp (value nil))
           (t (value t)))))

(defmacro prove$ (term &key
                       hints instructions otf-flg
                       (with-output '(:off :all :gag-mode nil))
                       time-limit
                       step-limit
                       (ignore-ok 'nil ignore-ok-p)
                       (with-translate-error 't))

; All of the arguments except :with-output are evaluated.  The result is
; (mv nil t state) if the proof is successful, otherwise (mv nil nil state).

  (declare (xargs :guard (member-eq ignore-ok '(t nil :warn))))
  (let* ((form `(prove$-fn ,term state ,hints ,instructions ,otf-flg
                           ,ignore-ok ,ignore-ok-p ,with-translate-error))
         (form `(with-output! ,@with-output ,form))
         (form (if time-limit
                   `(with-prover-time-limit ,time-limit ,form)
                 form))
         (form (if step-limit
                   `(with-prover-step-limit! ,step-limit ,form)
                 form)))
    `(prove$-return ,form)))

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
 (prove$ term                  ; any term (translated or not)
         &key
         hints                 ; default nil
         instructions          ; default nil
         ignore-ok             ; default taken from acl2-defaults-table
         otf-flg               ; default nil
         with-output           ; default (:off :all :gag-mode nil)
         time-limit            ; default nil
         step-limit            ; default nil
         with-translate-error) ; default t
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
 on @('with-output').</p>

 <p>@('Prove$') returns an @(see error-triple), @('(mv erp val state)'), where
 @('val') is @('t') when @('term') is successfully proved, else @('nil').  By
 default, @('erp') is non-@('nil') if the given @('term') or @('hints') have
 illegal syntax, in which case a suitable error message is printed; otherwise
 @('erp') is @('nil') and the error message is only printed if error output is
 turned on by the @(':with-output') argument.  That default behavior is
 overridden if @(':with-translate-error') is supplied a value of @('nil'); in
 that case, @('erp') is always @('nil') and error messages are suppressed
 unless the @(':with-output') argument is supplied and allows them.</p>

 <p>Note that after evaluation of a @('prove$') call, you can evaluate the form
 @('(prover-steps-counted state)') to get the number of prover steps that were
 taken &mdash; except, a negative number indicates a step-limit violation.  See
 @(See prover-steps-counted).</p>")
