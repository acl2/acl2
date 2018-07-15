; Event-Level Evaluation
;
; Copyright (C) 2018 Regents of the University of Texas
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)
;   Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we define macros that employ make-event to check evaluations of forms.
; See community book make-event/eval-tests.lisp (and many other .lisp files in
; that directory) for how these macros may be employed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-eval-to
  :parents (testing-utilities errors)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a form evaluates to a non-erroneous error triple
          with the value of a specified expression."
  :long
  "@({
     (must-eval-to form
                   expr
                   :ld-skip-proofsp ...
                   :with-output-off ...
                   :check-expansion ....)
   })
   <p>
   @('Form') should evaluate to an error triple @('(mv erp val state)').
   If @('erp') is @('nil') and @('val') is the value of @('expr')
   then @('(must-eval-to form expr)') expands to @('(value-triple \'val)');
   otherwise expansion causes an appropriate soft error.
   Note that both @('form') and @('expr') are evaluated.
   </p>
   <p>
   The @(':ld-skip-proofsp') option sets the value of @(tsee ld-skip-proofsp)
   to use for evaluating @('form'),
   unless it is @(':default'), which is the default,
   in which case @(tsee ld-skip-proofsp) retains its current value.
   </p>
   <p>
   The @(':with-output-off') option serves to suppress output from @('form'):
   when not @('nil'), it is used as the @(':off') argument of @(tsee with-output).
   The default is @(':all'), i.e., all output is suppressed.
   </p>
   <p>
   The @(':check-expansion') option determines whether @('form')
   is re-run and re-checked at @(tsee include-book) time;
   see @(tsee make-event).
   By default, it is not.
   </p>
   @(def must-eval-to)")

(defmacro must-eval-to (&whole must-eval-to-form
                               form expr
                               &key
                               (ld-skip-proofsp ':default)
                               (with-output-off ':all)
                               (check-expansion 'nil check-expansion-p))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-eval-to-t
  :parents (testing-utilities errors must-eval-to)
  :short "A specialization of @(tsee must-eval-to) to ensure that
          a form evaluates to a non-erroneous error triple with value @('t')."
  :long
  "<p>
   This calls @(tsee must-eval-to) with @('t') as the @('expr') argument.
   @('Form') should evaluate to an error triple @('(mv erp val state)').
   If @('erp') is @('nil') and @('val') is @('t')
   then @('(must-eval-to form expr)') expands to @('(value-triple t)');
   otherwise expansion causes an appropriate soft error.
   </p>
   <p>
   The keyword arguments have the same meaning as in @(tsee must-eval-to).
   </p>
   @(def must-eval-to-t)")

(defmacro must-eval-to-t (form &key
                               (ld-skip-proofsp ':default)
                               (with-output-off ':all)
                               (check-expansion 'nil check-expansion-p))
  (declare (xargs :guard (booleanp check-expansion)))
  `(must-eval-to ,form t
                 :with-output-off ,with-output-off
                 ,@(and check-expansion-p
                        `(:check-expansion ,check-expansion))
                 ,@(and (not (eq ld-skip-proofsp :default))
                        `(:ld-skip-proofsp ,ld-skip-proofsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-succeed
  :parents (testing-utilities errors)
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
      (set-cbd 17))                ;;   (because 17 isn't a string)
})

<p>See also @(see must-fail).</p>

<h5>General form:</h5>

@({
     (must-succeed form
                   [:with-output-off items]  ;; default:  :all
                   [:check-expansion bool]
                   )
})

<p>The @('form') should evaluate to an @(see error-triple), which is true for
most top-level ACL2 events and other high level commands.</p>

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-succeed*

  :parents (testing-utilities errors must-succeed)

  :short "A variant of @(tsee must-succeed) that accepts multiple forms."

  :long

  "@({
     (must-succeed* form1
                    ...
                    formN
                    :with-output-off ...
                    :check-expansion ...)
   })

   <p>
   The @('N') forms must be
   <see topic='@(url embedded-event-form)'>embedded event forms</see>,
   because they are put into a @(tsee progn)
   so that earlier forms are evaluated
   before considering later forms in the sequence.
   This is a difference with @(tsee must-succeed),
   whose form is required to return
   an <see topic='@(url error-triple)'>error triple</see>
   without necessarily being an embedded event form;
   since @(tsee must-succeed) takes only one form,
   there is no issue of earlier forms being evaluated
   before considering later forms
   as in @(tsee must-succeed*).
   </p>

   <p>
   The forms may be followed by
   @(':with-output-off') and/or @(':check-expansion'),
   as in @(tsee must-succeed).
   </p>

   @(def must-succeed*)"

  (defmacro must-succeed* (&rest args)
    (mv-let (erp forms options)
      (partition-rest-and-keyword-args args
                                       '(:with-output-off :check-expansion))
      (if erp
          '(er hard?
               'must-succeed*
               "The arguments of MUST-SUCCEED* must be zero or more forms ~
                followed by the options :WITH-OUTPUT-OFF and :CHECK-EXPANSION.")
        (let ((with-output-off-pair (assoc :with-output-off options))
              (check-expansion-pair (assoc :check-expansion options)))
          `(must-succeed (progn ,@forms)
                         ,@(if with-output-off-pair
                               `(:with-output-off ,(cdr with-output-off-pair))
                             nil)
                         ,@(if check-expansion-pair
                               `(:check-expansion ,(cdr check-expansion-pair))
                             nil)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-fail
  :parents (testing-utilities errors)
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-local
  :parents (testing-utilities errors must-fail)
  :short "A @(see local) variant of @(tsee must-fail)."
  :long
  "<p>
   This is useful to overcome the problem discussed in the caveat
   in the documentation of @(tsee must-fail).
   </p>
   @(def must-fail-local)"
  (defmacro must-fail-local (&rest args)
    `(local (must-fail ,@args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-error
  :parents (testing-utilities errors must-fail)
  :short "A specialization of @(tsee must-fail) to ensure that an error occurs."

  :long "<p>Evaluation of @('(must-fail-with-error <form>)') returns without
 error exactly when evaluation of @('<form>') causes an error.</p>

 <p>See @(see must-fail) for more details, as @('must-fail-with-error')
 abbreviates @('must-fail') as follows.</p>

 @(def must-fail-with-error)

 <p>Also see @(see must-fail-with-soft-error) and
 @(see must-fail-with-hard-error).</p>"

  (defmacro must-fail-with-error (form &rest args)
    (list* 'must-fail form :expected :any args)))

;; deprecated:

(defsection ensure-error
  :parents (must-fail-with-error)
  :short "Deprecated synonym of @(tsee must-fail-with-error)"
  (defmacro ensure-error (&rest args)
    `(must-fail-with-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-soft-error
  :parents (testing-utilities errors must-fail)
  :short "A specialization of @(tsee must-fail) to ensure that
          a soft error occurs."

  :long "<p>Evaluation of @('(must-fail-with-soft-error <form>)') returns
 without error exactly when evaluation of @('<form>') causes a soft error.</p>

 <p>See @(see must-fail) for more details, as @('must-fail-with-soft-error')
 abbreviates @('must-fail') as follows.</p>

 @(def must-fail-with-soft-error)

 <p>Also see @(see must-fail-with-error) and
 @(see must-fail-with-hard-error).</p>"

  (defmacro must-fail-with-soft-error (form &rest args)
    (list* 'must-fail form :expected :soft args)))

;; deprecated:

(defsection ensure-soft-error
  :parents (must-fail-with-soft-error)
  :short "Deprecated synonym of @(tsee must-fail-with-soft-error)"
  (defmacro ensure-soft-error (&rest args)
    `(must-fail-with-soft-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-fail-with-hard-error
  :parents (testing-utilities errors must-fail)
  :short "A specialization of @(tsee must-fail) to ensure that
          a hard error occurs."

  :long "<p>Evaluation of @('(must-fail-with-hard-error <form>)') returns
 without error exactly when evaluation of @('<form>') causes a hard error.</p>

 <p>See @(see must-fail) for more details, as @('must-fail-with-hard-error')
 abbreviates @('must-fail') as follows.</p>

 @(def must-fail-with-hard-error)

 <p>Also see @(see must-fail-with-error) and
 @(see must-fail-with-soft-error).</p>"

  (defmacro must-fail-with-hard-error (form &rest args)
    (list* 'must-fail form :expected :hard args)))

;; deprecated:

(defsection ensure-hard-error
  :parents (must-fail-with-hard-error)
  :short "Deprecated synonym of @(tsee must-fail-with-hard-error)"
  (defmacro ensure-hard-error (&rest args)
    `(must-fail-with-hard-error ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-prove
  :parents (testing-utilities errors)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a formula gets proved."
  :long
  "<p>
   This takes the same arguments as @(tsee thm).
   It wraps the @(tsee thm) into a @(tsee must-succeed).
   </p>
   @(def must-prove)"

  (defmacro must-prove (&rest args)
    `(must-succeed (thm ,@args))))

;; deprecated:

(defsection thm?
  :parents (must-prove)
  :short "Deprecated synonym of @(tsee must-prove)."
  (defmacro thm? (&rest args)
    `(must-prove ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-not-prove
  :parents (testing-utilities errors)
  :short "A top-level @(tsee assert$)-like command to ensure that
          a formula does not get proved."
  :long
  "<p>
   This takes the same arguments as @(tsee thm).
   It wraps the @(tsee thm) into a @(tsee must-fail).
   </p>
   @(def must-not-prove)"

  (defmacro must-not-prove (&rest args)
    `(must-fail (thm ,@args))))

;; deprecated:

(defsection not-thm?
  :parents (must-not-prove)
  :short "Deprecated synonym of @(tsee must-not-prove)."
  (defmacro not-thm? (&rest args)
    `(must-not-prove ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection must-be-redundant
  :parents (testing-utilities errors)
  :short "A top-level @(tsee assert$)-like command
          to ensure that given forms are redundant."
  :long
  "<p>
   The forms are put into an @(tsee encapsulate),
   along with a @(tsee set-enforce-redundancy) command that precedes them.
   </p>
   @(def must-be-redundant)"
  (defmacro must-be-redundant (&rest forms)
    `(encapsulate
       ()
       (set-enforce-redundancy t)
       ,@forms)))
