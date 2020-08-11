; Event Macros Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc-constructors")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ event-macro-proof-preparation
  :parents (event-macros)
  :short "Proof preparation for event macros."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some event macros generate ACL2 proofs that are expected to never fail.
     These proofs consist of carefully architected @(see hints)
     where only certain explicitly specified rules are enabled,
     and which may make use of the event macro's "
    (xdoc::seetopic "event-macro-applicability-conditions"
                    "applicabiity conditions")
    ".")
   (xdoc::p
    "The expectation that these generated proofs never fail
     may not be met if the carefully architected hints are ``sabotaged''
     by things like default hints or special treatment of built-in functions
     (e.g. functions that get expanded
     even if their definition is disabled.
     Thus, an event macro should generate, prior to the proofs in question,
     events that eliminate these possible saboteurs.
     These are preparatory events for the proofs.")
   (xdoc::p
    "Here we provide a utility to do precisely that:
     prepare (various ACL2 settings) for (generated) proofs.
     This utility is meant to be used inside an @(tsee encapsulate):
     the preparatory events are local to the @(tsee encapsulate).
     This utility prepares certain settings;
     these may not be exhaustive,
     and thus we may extend this utility to prepare more settings."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ evmac-prepare-proofs ()
  :short "Events to prepare proof generation."
  :long
  (xdoc::topstring-p
   "We disable the default and override hints;
    these are implicitly local events.
    We also add an explicitly local event to prevent @(tsee mv-nth)
    from being expanded,
    which is accomplished via a system attachment.")
  '(progn
     (set-default-hints nil)
     (set-override-hints nil)
     (local
      (defattach-system simplifiable-mv-nth-p constant-nil-function-arity-0))))
