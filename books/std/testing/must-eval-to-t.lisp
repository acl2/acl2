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

(include-book "must-eval-to")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc must-eval-to-t

  :parents (std/testing errors must-eval-to)

  :short "A specialization of @(tsee must-eval-to) to ensure that
          a form evaluates to a non-erroneous error triple with value @('t')."

  :long

  "<p>This calls @(tsee must-eval-to) with @('t') as the @('expr') argument.
   @('Form') should evaluate to an error triple @('(mv erp val state)').
   If @('erp') is @('nil') and @('val') is @('t')
   then @('(must-eval-to form expr)') expands to @('(value-triple t)');
   otherwise expansion causes an appropriate soft error.</p>

   <p>The keyword arguments have the same meaning
   as in @(tsee must-eval-to).</p>

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
