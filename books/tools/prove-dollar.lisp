; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2006)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defmacro with-error-output? (flg form)
  `(if ,flg
       (with-output! :on error ,form)
     ,form))

(defun prove$-fn (term state hints otf-flg with-translate-error)

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
        (er-let* ((hints (translate-hints+ 'thm
                                           hints
                                           (default-hints wrld)
                                           ctx wrld state))
                  (tterm (translate term t t t ctx wrld state)))
          (value (cons hints tterm))))
       (cond
        ((and erp with-translate-error)
         (mv :translate-error :translate-error state))
        (t (let ((hints (car val))
                 (tterm (cdr val)))
; known-stobjs = t (stobjs-out = t)
             (state-global-let*
              ((abort-soft nil)) ; interrupts abort immediately to the top level
              (prove tterm
                     (make-pspv ens wrld state
                                :displayed-goal term
                                :otf-flg otf-flg)
                     hints ens wrld ctx state)))))))))

(defmacro prove$-return (form)
  `(mv-let (erp val state)
     ,form
     (cond ((and (eq erp :translate-error)
                 (eq val :translate-error))
            (silent-error state))
           (erp (value nil))
           (t (value t)))))

(defmacro prove$ (term &key
                       hints otf-flg
                       (with-output '(:off :all :gag-mode nil))
                       time-limit
                       step-limit
                       (with-translate-error 't))

; All of the arguments except :with-output are evaluated.  The result is
; (mv nil t state) if the proof is successful, otherwise (mv nil nil state).

  (let* ((form `(prove$-fn ,term state ,hints ,otf-flg ,with-translate-error))
         (form `(with-output! ,@with-output ,form))
         (form (if time-limit
                   `(with-prover-time-limit ,time-limit ,form)
                 form))
         (form (if step-limit
                   `(with-prover-step-limit! ,step-limit ,form)
                 form)))
    `(prove$-return ,form)))

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
         otf-flg               ; default nil
         with-output           ; default (:off :all :gag-mode nil)
         time-limit            ; default nil
         step-limit            ; default nil
         with-translate-error) ; default t
 })

 <p>where all arguments except @('with-output') are evaluated.  The value of
 keyword @(':with-output'), if supplied, should be a list containing arguments
 one would give to the macro, @(tsee with-output), hence a list that satisfies
 @(tsee keyword-value-listp).  The @(tsee hints), @(tsee otf-flg), @(tsee
 time-limit), and @(tsee step-limit) arguments are as one would expect for
 calls of the prover.</p>

 <p>@('Prove$') returns an @(see error-triple), @('(mv erp val state)'), where
 @('val') is @('t') when @('term') is successfully proved, else @('nil').  By
 default, @('erp') is non-@('nil') if the given @('term') or @('hints') have
 illegal syntax, in which case a suitable error message is printed; otherwise
 @('erp') is @('nil') and the error message is only printed if error output is
 turned on by the @(':with-output') argument.  That default behavior is
 overridden if @(':with-translate-error') is supplied a value of @('nil'); in
 that case, @('erp') is always @('nil') and error messages are suppressed
 unless the @(':with-output') argument is supplied and allows them.</p>")
