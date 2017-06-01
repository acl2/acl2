; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc trans-eval-error-triple
  :parents (system-utilities)
  :short "An ACL2 evaluator for forms that return @(see error-triple)s"
  :long "@({
 General Form:

 (trans-eval-error-triple form ctx state)

 })

 <p>where @('form') is a form that evaluates to an @(see error-triple),
 @('ctx') is a context (see @(see ctx)), and @('state') is the ACL2 @(see
 state).  If @('form') is syntactically illegal, then
 @('(mv :trans-error :trans-error state)') is returned.  Otherwise,
 evaluation of @('form') should produce an error-triple @('(mv erp val
 state)'), and that error-triple is returned.</p>")

(defun trans-eval-error-triple (form ctx state)

; This function translates and evaluates form, which should return an error
; triple (mv erp val state); see :DOC error-triple.  Attachments are allowed.
; If there is no error then (mv nil val state) is returned; if an error occurs
; in the translation process then (mv :trans-error :trans-error state) is
; returned; and otherwise, (mv erp val state) is returned where erp and val are
; as above.

  (declare (xargs :mode :program :stobjs state))
  (mv-let (trans-erp stobjs-out/replaced-val state)
    (trans-eval form ctx state t)
    (cond (trans-erp (mv :trans-error :trans-error state))
          (t (let ((stobjs-out (car stobjs-out/replaced-val))
                   (triple (cdr stobjs-out/replaced-val)))
               (cond ((not (equal stobjs-out '(nil nil state)))
                      (er soft ctx
                          "The form ~x0, which was supplied to ~x1, does not ~
                           evaluate to an error triple."
                          form 'trans-eval-error-triple))
                     (t (mv (car triple) (cadr triple) state))))))))
