; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "invariant-max-faulty")
(include-book "operations-fault-tolerance")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-fault-tolerance
  :parents (correctness)
  :short "Invariant that fault tolerance does not change."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value of the predicate @(tsee fault-tolerant-p)
     does not change in the course of the execution.
     The predicate is defined in terms of the number of faulty validators,
     which is the cardinality of the set of addresses of faulty validators,
     which does not change as proved in @(see invariant-addresses),
     and in terms of the maximum number of faulty validators,
     which does not change as proved in @(see invariant-max-faulty).")
   (xdoc::p
    "This is a transition invariant,
     i.e. it related the old and new states of transitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fault-tolerant-p-of-next
  :short "The fault tolerance of the system is unchanged by all transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that for each kind of event, and then for generic events.
     That last theorem could be proved directly
     by enabling all the @('-possiblep') and @('-next') functions,
     but the theorems about the different kinds of events
     are useful in proofs of other invariants,
     which are formulated and proved separately
     for the different kinds of events."))

  (defrule fault-tolerant-p-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (fault-tolerant-p
                     (create-certificate-next cert systate))
                    (fault-tolerant-p systate)))
    :enable (fault-tolerant-p
             number-faulty))

  (defrule fault-tolerant-p-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (fault-tolerant-p
                     (receive-certificate-next msg systate))
                    (fault-tolerant-p systate)))
    :enable (fault-tolerant-p
             number-faulty))

  (defrule fault-tolerant-p-of-store-certificate-next
    (implies (store-certificate-possiblep val cert systate)
             (equal (fault-tolerant-p
                     (store-certificate-next val cert systate))
                    (fault-tolerant-p systate)))
    :enable (fault-tolerant-p
             number-faulty))

  (defrule fault-tolerant-p-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (fault-tolerant-p
                     (advance-round-next val systate))
                    (fault-tolerant-p systate)))
    :enable (fault-tolerant-p
             number-faulty))

  (defrule fault-tolerant-p-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (fault-tolerant-p
                     (commit-anchors-next val systate))
                    (fault-tolerant-p systate)))
    :enable (fault-tolerant-p
             number-faulty))

  (defrule fault-tolerant-p-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (fault-tolerant-p
                     (timer-expires-next val systate))
                    (fault-tolerant-p systate)))
    :enable (fault-tolerant-p
             number-faulty))

  (defrule fault-tolerant-p-of-event-next
    (implies (event-possiblep event systate)
             (equal (fault-tolerant-p (event-next event systate))
                    (fault-tolerant-p systate)))
    :enable (event-possiblep
             event-next)))
