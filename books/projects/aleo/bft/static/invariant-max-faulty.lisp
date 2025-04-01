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

(include-book "invariant-addresses")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-max-faulty
  :parents (correctness)
  :short "Invariant that the maximum tolerated number of faulty validators
          does not change."
  :long
  (xdoc::topstring
   (xdoc::p
    "As proved in the "
    (xdoc::seetopic "invariant-addresses"
                    "invariant that validator addresses do not change")
    ", the set of all, correct, and faulty validators
     is not changed by state transitions.
     Consequently, the number of all, correct, and faulty validators
     is not changed by state transitions.
     In particular, the maximum number of faulty validators,
     which is defined from the total number of validators,
     is not changed by state transitions.")
   (xdoc::p
    "This is a transition invariant,
     i.e. it relates the old and new states of transitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection invariant-max-faulty-theorems
  :short "Theorems saying that the maximum tolerated number of faulty validators
          is unchanged by transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove separate theorems for the different kinds of events,
     since these are useful in other proofs.
     We also prove the top-level theorem for all kinds of events."))

  (local (in-theory (enable in-all-addresses-when-in-correct-addresses)))

  (defrule max-faulty-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (max-faulty (create-certificate-next cert systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             create-certificate-possiblep
             create-certificate-next))

  (defrule max-faulty-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (max-faulty (receive-certificate-next msg systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             receive-certificate-possiblep
             receive-certificate-next))

  (defrule max-faulty-of-store-certificate-next
    (implies (store-certificate-possiblep cert val systate)
             (equal (max-faulty (store-certificate-next cert val systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             store-certificate-possiblep
             store-certificate-next))

  (defrule max-faulty-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (max-faulty (advance-round-next val systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             advance-round-possiblep
             advance-round-next))

  (defrule max-faulty-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (max-faulty (commit-anchors-next val systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             commit-anchors-possiblep
             commit-anchors-next))

  (defrule max-faulty-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (max-faulty (timer-expires-next val systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             timer-expires-possiblep
             timer-expires-next))

  (defrule max-faulty-of-event-next
    (implies (event-possiblep val systate)
             (equal (max-faulty (event-next val systate))
                    (max-faulty systate)))
    :enable (max-faulty
             number-validators
             event-possiblep
             event-next)))
