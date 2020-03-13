; Standard Testing Library
;
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "must-eval-to-t")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-fail
  :parents (std/testing errors)
  :short "A top-level @(see assert$)-like command.  Ensures that a command
which returns an @(see error-triple)&mdash;e.g., @(see defun) or @(see
defthm)&mdash;will not be successful."

  :long "<p>This can be useful for adding simple unit tests of macros,
theories, etc. to your books.  Basic examples:</p>

@({
    (must-fail                      ;; succeeds
      (defun 5))                    ;;   (invalid defun will indeed fail)

    (must-fail                      ;; causes an error
      (thm t))                      ;;   (because this thm proves fine)

    (must-fail (mv nil (hard-error 'foo \"MESSAGE\" nil) state))
                                    ;; causes an error
                                    ;;   (because hard errors propagate past
                                    ;;    must-fail by default)

    (must-fail (mv nil (hard-error 'foo \"MESSAGE\" nil) state)
               :expected :hard)     ;; succeeds

    (must-fail                      ;; causes an error
      (in-theory (enable floor)))   ;;   (because this works fine)

    (must-fail                      ;; causes an error
      (* 3 4))                      ;;   (doesn't return an error triple)
})

<p>Must-fail is almost just like @(see must-succeed), except that the event is
expected to fail instead of succeed.  The option @(':expected') is described
below; for everything else, please see the documentation for @('must-succeed')
for syntax, options, and additional discussion.</p>

<p>Also see @(see must-fail-with-error), @(see must-fail-with-soft-error), and
@(see must-fail-with-hard-error), which are essentially aliases for
@('must-fail') with different values for the option, @(':expected'), which we
now describe.</p>

<p>When the value of keyword @(':expected') is @(':any'), then @('must-fail')
succeeds if and only if ACL2 causes an error during evaluation of the supplied
form.  However @(':expected') is @(':soft') by default, in which case success
requires that the error is ``soft'', not ``hard'': hard errors are caused by
guard violations, by calls of @(tsee illegal) and @(tsee hard-error), and by
calls of @(tsee er) that are not ``soft''.  Finally, if @(':expected') is
@(':hard'), then the call of @('must-fail') succeeds if and only if evaluation
of the form causes a hard error.</p>

<p>CAVEAT: If a book contains a non-@(see local) form that causes proofs to be
done, such as one of the form @('(must-fail (thm ...))'), then it might not be
possible to include that book.  That is because proofs are generally skipped
during @(tsee include-book), and any @('thm') will succeed if proofs are
skipped.  One fix is to make such forms @(see local).  Another fix is to use a
wrapper @(tsee must-fail!) that creates a call of @('must-fail') with
@(':check-expansion') to @('t'); that causes proofs to be done even when
including a book (because of the way that @('must-fail') is implemented using
@(tsee make-event)).</p>")

(defun error-from-eval-fn (form ctx aok)
  `(let ((form ',form)
         (ctx ,ctx)
         (aok ,aok))
     (mv-let (erp stobjs-out/replaced-val state)
       (trans-eval form ctx state aok)
       (let ((stobjs-out (car stobjs-out/replaced-val))
             (replaced-val (cdr stobjs-out/replaced-val)))
         (cond (erp (value :hard)) ; no stobjs-out to obtain in this case
               ((not (equal stobjs-out
                            '(nil nil state)))
                (value (er hard ctx
                           "The given form must return an error triple, but ~
                            ~x0 does not.  See :DOC error-triple."
                           form)))
               (t (value (and (car replaced-val)
                              :soft))))))))

(defmacro error-from-eval (form &optional
                                (ctx ''hard-error-to-soft-error)
                                (aok 't))

; Returns :hard for hard error, :soft for soft error, and nil for no error.

  (error-from-eval-fn form ctx aok))

(defmacro must-fail (&whole must-fail-form
                            form
                            &key
                            (expected ':soft) ; :soft, :hard, or :any
                            (with-output-off ':all)
                            (check-expansion 'nil check-expansion-p))

; Form should evaluate to an error triple (mv erp val state).  (Must-fail
; form) expands to (value-triple t) if erp is non-nil, and expansion causes a
; soft error otherwise.

; Remark on provisional certification: By default we bind state global
; ld-skip-proofsp to nil when generating the .acl2x file for this book during
; provisional certification.  We do this because in some cases must-fail
; expects proofs to fail.  Some books in the distributed books/make-event/
; directory have the following comment when this change was necessary for
; .acl2x file generation during provisional certification:
; "; See note about ld-skip-proofsp in the definition of must-fail."

  (declare (xargs :guard (member-eq expected '(:soft :hard :any))))
  (let ((form (case-match expected
                (:soft form)
                (& `(error-from-eval ,form))))
        (success (case-match expected
                   (:soft '(not (eq erp nil)))
                   (:hard '(eq val :hard))
                   (& ; :any, so val should be :hard or :soft, not nil
                    '(not (eq val nil))))))
    `(make-event
      '(must-eval-to-t
        (mv-let (erp val state)
          ,form
          (declare (ignorable erp val))
          (value ,success))
        :ld-skip-proofsp
        (if (eq (cert-op state) :write-acl2xu)
            nil
          (f-get-global 'ld-skip-proofsp state))
        :with-output-off ,with-output-off
        ,@(and check-expansion-p
               `(:check-expansion ,check-expansion)))
      :on-behalf-of ,must-fail-form)))
