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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-addresses
  :parents (correctness)
  :short "Invariant that validator addresses do not change."
  :long
  (xdoc::topstring
   (xdoc::p
    "The sets of the addresses of
     all validators,
     all correct validators,
     and all faulty validators
     do not change in the course of the protocol.
     That is, the identities of validators,
     and their correct vs. faulty status,
     remain constant during the protocol,
     although their internal states may obviously change.")
   (xdoc::p
    "These are transition invariants,
     i.e. they relate the old and new states of transitions.")
   (xdoc::p
    "The proofs are straightforward,
     based on how transitions are defined.
     Transitions only change validator states (the values of the map),
     but never the validator addresses (the keys of the map).
     Furthermore, they never change validator states into @('nil')
     (which would change a correct validator into a faulty one),
     and never turn @('nil') into some validator state
     (which would change a faulty validator into a correct one)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection invariant-all-addresses
  :short "The set of the addresses of all the validators
          is unchanged by all transitions."
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

  (local (in-theory (enable in-all-addresses-when-in-correct-addresses)))

  (defrule all-addresses-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (all-addresses
                     (create-certificate-next cert systate))
                    (all-addresses systate)))
    :enable (create-certificate-possiblep
             create-certificate-next))

  (defrule all-addresses-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (all-addresses
                     (receive-certificate-next msg systate))
                    (all-addresses systate)))
    :enable (receive-certificate-possiblep
             receive-certificate-next))

  (defrule all-addresses-of-store-certificate-next
    (implies (store-certificate-possiblep cert val systate)
             (equal (all-addresses
                     (store-certificate-next cert val systate))
                    (all-addresses systate)))
    :enable (store-certificate-possiblep
             store-certificate-next))

  (defrule all-addresses-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (all-addresses
                     (advance-round-next val systate))
                    (all-addresses systate)))
    :enable (advance-round-possiblep
             advance-round-next))

  (defrule all-addresses-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (all-addresses
                     (commit-anchors-next val systate))
                    (all-addresses systate)))
    :enable (commit-anchors-possiblep
             commit-anchors-next))

  (defrule all-addresses-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (all-addresses
                     (timer-expires-next val systate))
                    (all-addresses systate)))
    :enable (timer-expires-possiblep
             timer-expires-next))

  (defrule all-addresses-of-event-next
    (implies (event-possiblep event systate)
             (equal (all-addresses (event-next event systate))
                    (all-addresses systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection invariant-correct-addresses
  :short "The set of the addresses of all the correct validators
          is unchanged by all transitions."
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

  (defrule correct-addresses-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (correct-addresses
                     (create-certificate-next cert systate))
                    (correct-addresses systate)))
    :enable (create-certificate-possiblep
             create-certificate-next))

  (defrule correct-addresses-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (correct-addresses
                     (receive-certificate-next msg systate))
                    (correct-addresses systate)))
    :enable (receive-certificate-possiblep
             receive-certificate-next))

  (defrule correct-addresses-of-store-certificate-next
    (implies (store-certificate-possiblep cert val systate)
             (equal (correct-addresses
                     (store-certificate-next cert val systate))
                    (correct-addresses systate)))
    :enable (store-certificate-possiblep
             store-certificate-next))

  (defrule correct-addresses-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (correct-addresses
                     (advance-round-next val systate))
                    (correct-addresses systate)))
    :enable (advance-round-possiblep
             advance-round-next))

  (defrule correct-addresses-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (correct-addresses
                     (commit-anchors-next val systate))
                    (correct-addresses systate)))
    :enable (commit-anchors-possiblep
             commit-anchors-next))

  (defrule correct-addresses-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (correct-addresses
                     (timer-expires-next val systate))
                    (correct-addresses systate)))
    :enable (timer-expires-possiblep
             timer-expires-next))

  (defrule correct-addresses-of-event-next
    (implies (event-possiblep event systate)
             (equal (correct-addresses (event-next event systate))
                    (correct-addresses systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection invariant-faulty-addresses
  :short "The set of the addresses of all the faulty validators
          is unchanged by all transitions."
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

  (defrule faulty-addresses-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (faulty-addresses
                     (create-certificate-next cert systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses)

  (defrule faulty-addresses-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (faulty-addresses
                     (receive-certificate-next msg systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses)

  (defrule faulty-addresses-of-store-certificate-next
    (implies (store-certificate-possiblep cert val systate)
             (equal (faulty-addresses
                     (store-certificate-next cert val systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses)

  (defrule faulty-addresses-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (faulty-addresses
                     (advance-round-next val systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses)

  (defrule faulty-addresses-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (faulty-addresses
                     (commit-anchors-next val systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses)

  (defrule faulty-addresses-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (faulty-addresses
                     (timer-expires-next val systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses)

  (defrule faulty-addresses-of-event-next
    (implies (event-possiblep event systate)
             (equal (faulty-addresses (event-next event systate))
                    (faulty-addresses systate)))
    :enable (event-possiblep
             event-next)))
