; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

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

(defsection invariant-validator-addresses
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

  (defrule validator-addresses-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (validator-addresses
                     (create-certificate-next cert systate))
                    (validator-addresses systate)))
    :enable (create-certificate-possiblep
             create-certificate-next))

  (defrule validator-addresses-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (validator-addresses
                     (receive-certificate-next msg systate))
                    (validator-addresses systate)))
    :enable (receive-certificate-possiblep
             receive-certificate-next))

  (defrule validator-addresses-of-store-certificate-next
    (implies (store-certificate-possiblep cert val systate)
             (equal (validator-addresses
                     (store-certificate-next cert val systate))
                    (validator-addresses systate)))
    :enable (store-certificate-possiblep
             store-certificate-next))

  (defrule validator-addresses-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (validator-addresses
                     (advance-round-next val systate))
                    (validator-addresses systate)))
    :enable (advance-round-possiblep
             advance-round-next))

  (defrule validator-addresses-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (validator-addresses
                     (commit-anchors-next val systate))
                    (validator-addresses systate)))
    :enable (commit-anchors-possiblep
             commit-anchors-next))

  (defrule validator-addresses-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (validator-addresses
                     (timer-expires-next val systate))
                    (validator-addresses systate)))
    :enable (timer-expires-possiblep
             timer-expires-next))

  (defrule validator-addresses-of-event-next
    (implies (event-possiblep event systate)
             (equal (validator-addresses (event-next event systate))
                    (validator-addresses systate)))
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
    "Unlike for the other validator address sets (all and correct),
     here we just prove one theorem for all kinds of events.
     The set of addresses of faulty validator
     is not used much in formulating and proving other invariants so far.
     If that changes, we can add similar theorems for faulty validators
     for each different kind of events."))

  (defrule faulty-addresses-of-event-next
    (implies (event-possiblep event systate)
             (equal (faulty-addresses (event-next event systate))
                    (faulty-addresses systate)))
    :enable faulty-addresses))
