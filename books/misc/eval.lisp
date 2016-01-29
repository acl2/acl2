; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we define macros that employ make-event to check evaluations of forms.
; See community book make-event/eval-tests.lisp (and many other .lisp files in
; that directory) for how these macros may be employed.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defmacro must-eval-to (&whole must-eval-to-form
                               form expr
                               &key
                               (ld-skip-proofsp ':default)
                               (with-output-off ':all)
                               (check-expansion 'nil check-expansion-p))

; Form should evaluate to an error triple (mv erp form-val state).  If erp is
; nil and expr-val is the value of expr then (must-eval-to form expr) expands
; to (value-triple 'expr-val); otherwise expansion causes an appropriate soft
; error.  Note that both form and expr are evaluated.

  (declare (xargs :guard (booleanp check-expansion)))
  (let* ((body
          `(er-let* ((form-val-use-nowhere-else ,form))
             (let ((expr-val (check-vars-not-free
                              (form-val-use-nowhere-else)
                              ,expr)))
               (cond ((equal form-val-use-nowhere-else expr-val)
                      (value (list 'value-triple (list 'quote expr-val))))
                     (t (er soft
                            (msg "( MUST-EVAL-TO ~@0 ~@1)"
                                 (tilde-@-abbreviate-object-phrase ',form)
                                 (tilde-@-abbreviate-object-phrase ',expr))
                            "Evaluation returned ~X01, not the value ~x2 of ~
                            the expression ~x3."
                            form-val-use-nowhere-else
                            (evisc-tuple 4 3 nil nil)
                            expr-val
                            ',expr))))))
         (form `(make-event ,(if (eq ld-skip-proofsp :default)
                                 body
                               `(state-global-let*
                                 ((ld-skip-proofsp ,ld-skip-proofsp))
                                 ,body))
                            :on-behalf-of ,must-eval-to-form
                            ,@(and check-expansion-p
                                   `(:check-expansion ,check-expansion)))))
    (cond (with-output-off `(with-output :off ,with-output-off ,form))
          (t form))))

(defmacro must-eval-to-t (form &key
                               (ld-skip-proofsp ':default)
                               (with-output-off ':all)
                               (check-expansion 'nil check-expansion-p))

; Form should evaluate to an error triple (mv erp val state).  If erp is nil
; and val is t then (must-eval-to-t form) expands to (value-triple t);
; otherwise expansion causes an appropriate soft error.

  (declare (xargs :guard (booleanp check-expansion)))
  `(must-eval-to ,form t
                 :with-output-off ,with-output-off
                 ,@(and check-expansion-p
                        `(:check-expansion ,check-expansion))
                 ,@(and (not (eq ld-skip-proofsp :default))
                        `(:ld-skip-proofsp ,ld-skip-proofsp))))

(defxdoc must-succeed
  :parents (errors)
  :short "A top-level @(see assert$)-like command.  Ensures that a command
which returns an @(see error-triple)&mdash;e.g., a @(see defun) or
@(see defthm)&mdash;will return successfully."

  :long "<p>This can be useful for adding simple unit tests of macros,
theories, etc. to your books.  Basic examples:</p>

@({
    (must-succeed                  ;; works fine
      (defun f (x) (consp x)))     ;;   (NOTE: F not defined afterwards!)

    (must-succeed                  ;; causes an error
      (defthm bad-theorem nil))    ;;   (unless we can prove NIL!)

    (must-succeed                  ;; causes an error
      (set-gag-mode 42))           ;;   (because 42 isn't a gag mode)
})

<p>See also @(see must-fail).</p>

<h5>General form:</h5>

@({
     (must-succeed form
                   [:with-output-off items]  ;; default:  :all
                   [:check-expansion bool]
                   )
})

<p>The @('form') should typically be a form that returns an @(see
error-triple), which is true for most top-level ACL2 events and other high
level commands.</p>

<p>The @('form') is submitted in a @(see make-event), which has a number of
consequences.  Most importantly, when @('form') is an event like a @(see
defun), or @(see defthm), it doesn't persist after the @(see must-succeed)
form.  Other state updates do persist, e.g.,</p>

@({
     (must-succeed (assign foo 5))   ;; works fine
     (@ foo)                         ;; 5
})

<p>See the @(see make-event) documentation for details.</p>

<h5>Options</h5>

<p><b>with-output-off</b>.  By default, all output from @('form') is
suppressed, but you can customize this.  Typical example:</p>

@({
     (must-succeed
       (defun f (x) (consp x))
       :with-output-off nil)    ;; don't suppress anything
})

<p><b>check-expansion</b>.  By default the form won't be re-run and re-checked
at @(see include-book) time.  But you can use @(':check-expansion') to
customize this, as in @(see make-event).</p>

<p>Also see @(see must-succeed!).</p>")

(defmacro must-succeed (&whole must-succeed-form
                               form
                               &key
                               (with-output-off ':all)
                               (check-expansion 'nil check-expansion-p))

; (Must-succeed form) expands to (value-triple t) if evaluation of form is an
; error triple (mv nil val state), and causes a soft error otherwise.

  `(make-event
    '(must-eval-to-t
      (mv-let (erp val state)
        ,form
        (declare (ignore val))
        (value (eq erp nil)))
      :with-output-off ,with-output-off
      ,@(and check-expansion-p
             `(:check-expansion ,check-expansion)))
    :on-behalf-of ,must-succeed-form))

(defxdoc must-fail
  :parents (errors)
  :short "A top-level @(see assert$)-like command.  Ensures that a command
which returns an @(see error-triple)&mdash;e.g., @(see defun) or @(see
defthm)&mdash;will not be successful."

  :long "<p>This can be useful for adding simple unit tests of macros,
theories, etc. to your books.  Basic examples:</p>

@({
    (must-fail                     ;; works fine
      (defun 5))                   ;;   (invalid defun will indeed fail)

    (must-fail                     ;; causes an error
      (thm t))                     ;;   (because this thm proves fine)

    (must-fail                     ;; causes an error
      (in-theory (enable floor)))  ;;   (because this works fine)

    (must-fail                     ;; causes an error
      (* 3 4))                     ;;   (doesn't return an error triple)
})

<p>Must-fail is almost just like @(see must-succeed), except that the event is
expected to fail instead of succeed.  Please see the documentation for
@('must-succeed') for syntax, options, and additional discussion.</p>

<p>CAVEAT: If a book contains a non-@(see local) form that causes proofs to be
done, such as one of the form @('(must-fail (thm ...))'), then it might not be
possible to include that book.  That is because proofs are generally skipped
during @(tsee include-book), and any @('thm') will succeed if proofs are
skipped.  One fix is to make such forms @(see local).  Another fix is to use a
wrapper @(tsee must-fail!) that creates a call of @('must-fail') with
@(':check-expansion') to @('t'); that causes proofs to be done even when
including a book (because of the way that @('must-fail') is implemented using
@(tsee make-event)).</p>")

(defmacro must-fail (&whole must-fail-form
                            form
                            &key
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

  `(make-event
    '(must-eval-to-t
      (mv-let (erp val state)
        ,form
        (declare (ignore val))
        (value (not (eq erp nil))))
      :ld-skip-proofsp
      (if (eq (cert-op state) :write-acl2xu)
          nil
        (f-get-global 'ld-skip-proofsp state))
      :with-output-off ,with-output-off
      ,@(and check-expansion-p
             `(:check-expansion ,check-expansion)))
    :on-behalf-of ,must-fail-form))

(defmacro thm? (&rest args)
  `(must-succeed (thm ,@args)))

(defmacro not-thm? (&rest args)
  `(must-fail (thm ,@args)))
