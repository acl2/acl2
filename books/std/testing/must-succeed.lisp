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

(defxdoc must-succeed
  :parents (std/testing errors)
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
