; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "evaluation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ interpreter
  :parents (acl2-programming-language)
  :short "A program-mode interpreter."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an executable program-mode function
     that exhaustively calls @(tsee step);
     this program-mode function may not terminate.
     Then we define a wrapper that initializes the evaluation state
     with a function symbol and a list of argument values,
     same as the non-executable @(tsee exec-call) function.
     This can be used as an interpreter for
     the ACL2 programming language as formalized here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define interpret-loop ((estate eval-state-p) (program programp))
  :returns (value? "A @(tsee maybe-valuep).")
  :mode :program
  :short "Exhaustively apply @(tsee step) to an evaluation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We stop when we reach a final state or an error state.
     In the first case, we return the value in the final state.
     In the second case, we return @('nil').
     Or we may not terminate.")
   (xdoc::p
    "This is a program-mode executable counterpart of
     the logic-mode non-executable function @(tsee step*)."))
  (eval-state-case estate
                   :init (interpret-loop (step estate program) program)
                   :trans (interpret-loop (step estate program) program)
                   :final estate.result
                   :error nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define interpret ((function symbol-valuep)
                   (arguments value-listp)
                   (program programp))
  :returns (value? "A @(tsee maybe-valuep).")
  :mode :program
  :short "Exhaustively execute a function call."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a program-mode executable counterpart of
     the logic-mode non-executable function @(tsee exec-call).
     It is a possibly non-terminating interpreter."))
  (interpret-loop (eval-state-init function arguments) program))
