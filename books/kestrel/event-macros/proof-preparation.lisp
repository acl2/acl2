; Event Macros Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

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
     (e.g. functions that get expanded even if their definition is disabled).
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
  (xdoc::topstring
   (xdoc::p
    "We disable the "
    (xdoc::seetopic "default-hints" "default hints")
    " and "
    (xdoc::seetopic "override-hints" "override hints")
    "; these are implicitly local events.")
   (xdoc::p
    "We add an explicitly local event
     to prevent @(tsee mv-nth) from being expanded,
     which is accomplished via a system attachment.")
   (xdoc::p
    "We add an implicitly local event to set the "
    (xdoc::seetopic "set-dwp" "double-whammy property")
    " to @('nil').
     Since we mainly want to avoid dependencies on variable settings,
     we could equally set it to @('t') for that purpose.
     But we prefer the higher efficiency of setting it to @('nil'),
     also given that the generated proofs are crafted to always work,
     which should factor in the effort made by type reasoning.")
   (xdoc::p
    "We add an implicitly local event to set the "
    (xdoc::seetopic "induction-depth-limit" "induction depth limit")
    " to 1.
     This lets generated proofs by inductions work
     in case @(':induct') hints are not generated.
     It also prevents nested inductions from working,
     which arguably should not be used in generated proofs
     (or even in manual proofs).")
   (xdoc::p
    "We add an implicitly local event to suppress various warnings.
     This is useful when the generated events are printed in full."))
  '(progn
     (set-default-hints nil)
     (set-override-hints nil)
     (local
      (defattach-system simplifiable-mv-nth-p constant-nil-function-arity-0))
     (set-dwp nil)
     (set-induction-depth-limit 1)
     (set-inhibit-warnings "disable"
                           "double-rewrite"
                           "free"
                           "non-rec"
                           "subsume"
                           "theory"
                           "use")))
