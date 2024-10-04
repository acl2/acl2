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

(defxdoc+ invariant-quorum
  :parents (correctness)
  :short "Invariant that the quorum number does not change."
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
     is not changed by state transitions.
     And therefore the quorum number,
     defined as the difference between the total number of validators
     and the quorum number,
     is not changed by state transitions.")
   (xdoc::p
    "This is a transition invariant,
     i.e. it relates the old and new states of transitions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection invariant-quorum-theorems
  :short "Theorems saying that the quorum is unchanged by transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove separate theorems for the different kinds of events,
     since these are useful in other proofs.
     We also prove the top-level theorem for all kinds of events."))

  (local (in-theory (enable in-all-addresses-when-in-correct-addresses)))

  (defrule quorum-of-create-certificate-next
    (implies (create-certificate-possiblep cert systate)
             (equal (quorum (create-certificate-next cert systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             create-certificate-possiblep
             create-certificate-next))

  (defrule quorum-of-receive-certificate-next
    (implies (receive-certificate-possiblep msg systate)
             (equal (quorum (receive-certificate-next msg systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             receive-certificate-possiblep
             receive-certificate-next))

  (defrule quorum-of-store-certificate-next
    (implies (store-certificate-possiblep cert val systate)
             (equal (quorum (store-certificate-next cert val systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             store-certificate-possiblep
             store-certificate-next))

  (defrule quorum-of-advance-round-next
    (implies (advance-round-possiblep val systate)
             (equal (quorum (advance-round-next val systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             advance-round-possiblep
             advance-round-next))

  (defrule quorum-of-commit-anchors-next
    (implies (commit-anchors-possiblep val systate)
             (equal (quorum (commit-anchors-next val systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             commit-anchors-possiblep
             commit-anchors-next))

  (defrule quorum-of-timer-expires-next
    (implies (timer-expires-possiblep val systate)
             (equal (quorum (timer-expires-next val systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             timer-expires-possiblep
             timer-expires-next))

  (defrule quorum-of-event-next
    (implies (event-possiblep val systate)
             (equal (quorum (event-next val systate))
                    (quorum systate)))
    :enable (quorum
             number-validators
             max-faulty
             event-possiblep
             event-next)))
