; AIR Library
; Model 0: Input/Output Semantics
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "dynamic-semantics")

(local (include-book "std/lists/len" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ input/output-semantics
  :parents (model-0)
  :short "Input/output semantics of Model 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "By regarding the accumulator as containing
     the input to the program at the start of the execution
     and the output from the program at the end of the execution,
     we can characterize the input/output behavior of a program."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-output ((prog program-p) (input ubyte8p))
  :guard (and (program-well-formed-p prog)
              (terminatesp prog input))
  :returns (output ubyte8p)
  :short "Input/output function determined by a program."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since this language is deterministic,
     the input/output semantics of a program
     can be characterized as a function from the input to the output.")
   (xdoc::p
    "Although programs in M0 always terminate,
     we define the notion more generally,
     on terminating programs.")
   (xdoc::p
    "We create an initial state whose accumulator contains the input.
     We run the program to completion, using the minimum termination limit.
     We obtain the output from the accumulator in the final state."))
  (b* ((initial-st (make-vm-state :pc 0 :acc input :halted nil))
       (final-st (run initial-st prog (min-termination-limit prog input))))
    (vm-state->acc final-st)))
