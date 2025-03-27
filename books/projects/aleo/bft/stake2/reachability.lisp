; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ reachability
  :parents (definition)
  :short "Notion of reachable system states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define a notion of states reachable from other states,
     as well as a notion of states reachable from some initial state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-state-reachable-from-p ((systate system-statep)
                                          (from system-statep))
  :returns (yes/no booleanp)
  :short "Check if a system state is reachable from another one."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case when there is a list of zero or more events
     that are possible in the starting state (one after the other),
     and that lead to the state of interest (one after the other)."))
  (exists (events)
          (and (event-listp events)
               (events-possiblep events from)
               (equal (system-state-fix systate)
                      (events-next events from))))
  ///
  (fty::deffixequiv-sk system-state-reachable-from-p
    :args ((systate system-statep) (from system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-state-reachablep ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a system state is reachable from some initial state."
  (exists (from)
          (and (system-statep from)
               (system-initp from)
               (system-state-reachable-from-p systate from)))
  ///
  (fty::deffixequiv-sk system-state-reachablep
    :args ((systate system-statep))))
