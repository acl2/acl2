; Standard Testing Library
;
; Copyright (C) 2018 Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Matt Kaufmann (kaufmann@cs.utexas.edu)
; Contributing Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-eval-to

  :parents (std/testing errors)

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

   <p>@('Form') should evaluate to an error triple @('(mv erp val state)').
   If @('erp') is @('nil') and @('val') is the value of @('expr')
   then @('(must-eval-to form expr)') expands to @('(value-triple \'val)');
   otherwise expansion causes an appropriate soft error.
   Note that both @('form') and @('expr') are evaluated.</p>

   <p>The @(':ld-skip-proofsp') option sets the value of @(tsee ld-skip-proofsp)
   to use for evaluating @('form'),
   unless it is @(':default'), which is the default,
   in which case @(tsee ld-skip-proofsp) retains its current value.</p>

   <p>The @(':with-output-off') option serves to suppress output from @('form'):
   when not @('nil'),
   it is used as the @(':off') argument of @(tsee with-output).
   The default is @(':all'), i.e., all output is suppressed.</p>

   <p>The @(':check-expansion') option determines whether @('form')
   is re-run and re-checked at @(tsee include-book) time;
   see @(tsee make-event).
   By default, it is not.</p>

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
