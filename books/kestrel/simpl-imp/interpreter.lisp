; Simple Programming Language Imp Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SIMPL-IMP")

(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ interpreter
  :parents (imp-language)
  :short "An interpreter for Imp."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee stepn) can be used to run an Imp program for
     (at most) a given number of steps.
     The function @(tsee step*) defines exhaustive execution,
     but is not itself executable.
     Here we define a program-mode function that exhaustively executes
     the @(tsee step) function, until termination,
     or the program-mode function will not itself terminate."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exec ((cfg configp))
  :mode :program
  :short "Program-mode interpreter for Imp."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the configuration has no commands, we return the final environment.
     Otherwise, we step the configuration
     and we recursively call the interprete."))
  (if (consp (config->comms cfg))
      (exec (step cfg))
    (config->env cfg))
  :no-function t)
