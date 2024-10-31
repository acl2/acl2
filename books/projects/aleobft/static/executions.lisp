; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "initialization")
(include-book "transitions")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ executions
  :parents (definition)
  :short "Executions of the AleoBFT labeled state transition system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize executions in our labeled state transition systems
     via ACL2 functions to move from state to state in response to events.
     Based on this, we also define
     the notion of reachable states of the system."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step ((event eventp) (systate system-statep))
  :returns (systate? system-state-optionp)
  :short "Perform an execution step, corresponding to an event."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given an event and a state,
     return the new state resulting from the event
     if the event is possible in the old state;
     if the event is not possible, return @('nil')."))
  (if (event-possiblep event systate)
      (event-next event systate)
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step* ((events event-listp) (systate system-statep))
  :returns (systate? system-state-optionp)
  :short "Perform zero or more execution steps,
          corresponding to a list of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no events, we return the state unchanged.
     Otherwise, we execute the first event,
     and then the remaining events.
     If at any point an event is not possible, we return @('nil')."))
  (b* (((when (endp events)) (system-state-fix systate))
       (systate? (step (car events) systate))
       ((unless systate?) nil))
    (step* (cdr events) systate?))

  ///

  (defruled step*-of-nil
    (equal (step* nil systate)
           (system-state-fix systate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk reachablep ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a state is reachable,
          from some initial state via some sequence of events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initial states are always reachable,
     via the empty sequence of events."))
  (exists (systate0 events)
          (and (system-statep systate0)
               (system-state-initp systate0)
               (event-listp events)
               (equal systate (step* events systate0))))

  ///

  (defruled reachablep-when-system-state-initp
    (implies (and (system-statep systate)
                  (system-state-initp systate))
             (reachablep systate))
    :disable reachablep
    :use (:instance reachablep-suff
                    (systate0 systate)
                    (events nil))
    :enable step*-of-nil))
