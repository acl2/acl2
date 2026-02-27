; AIR Library
; Model 0: Static Semantics
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "AIR-M0")

(include-book "abstract-syntax")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-semantics
  :parents (model-0)
  :short "Static semantics of Model 0."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static semantics defines well-formedness conditions on programs.
     A well-formed M0 program must be non-empty.
     Additionally, we require that the program ends with a @('HALT')
     instruction for simplicity."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-nonempty-p ((prog program-p))
  :returns (yes/no booleanp)
  :short "Check that an M0 program is non-empty."
  (consp prog)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-ends-with-halt-p ((prog program-p))
  :returns (yes/no booleanp)
  :short "Check that an M0 program ends with a HALT instruction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This ensures the program will eventually halt.
     Since Model 0 has no jumps, ending with HALT guarantees termination."))
  :guard (consp prog)
  (opcode-case (car (last prog)) :halt))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define program-well-formed-p ((prog program-p))
  :returns (yes/no booleanp)
  :short "Check that an M0 program is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "A well-formed M0 program is non-empty and ends with @('HALT')."))
  (and (program-nonempty-p prog)
       (program-ends-with-halt-p prog))

  ///

  (defruled fetch-is-halt-when-last
    (implies (and (program-well-formed-p prog)
                  (natp pc)
                  (equal (1+ pc) (len prog)))
             (equal (fetch prog pc)
                    (opcode-halt)))
    :cases ((equal pc (1- (len prog))))
    :enable (program-nonempty-p
             program-ends-with-halt-p
             fetch
             nth-of-len-minus-1-is-car-last)))
