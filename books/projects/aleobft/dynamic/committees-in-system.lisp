; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-DYNAMIC")

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committees-in-system
  :parents (correctness)
  :short "Invariant that committees always consist of
          validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This invariant is mentioned in @(tsee update-committee-with-transaction),
     as the motivation for checking bonding transactions
     against the set of addresses of validators in the system.
     Here we formulate and prove the invariant.")
   (xdoc::p
    "The invariant applies to all committees
     calculated by all validators, based on their own blockchains,
     in the system state.
     Initially, only the genesis committee can be calculated,
     because the blockchains are all empty;
     the fact that the genesis committee consists of validators in the system
     is explicitly required in the characterization of the initial states"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk validator-committees-in-system-p ((vstate validator-statep)
                                             (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if all the committees calculable by a validator
          consist of members that are all validators in a given set."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here the validator is represented by its state @('vstate').
     The input @('all-vals') represents
     the addresseses of all the validators in the system:
     see @(tsee committees-in-system-p).")
   (xdoc::p
    "By `calculable committees' we mean active committees at rounds,
     because it is active committees that validators use to run the protocol.
     We say that for every round number,
     if there is a calculable committee at that round,
     its members are a subset of @('all-vals')."))
  (forall (round)
          (implies (posp round)
                   (b* ((blocks (validator-state->blockchain vstate))
                        (commtt (active-committee-at-round round
                                                           blocks
                                                           all-vals)))
                     (implies commtt
                              (set::subset (committee-members commtt)
                                           all-vals))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk committees-in-system-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          every committee calculable by every correct validator
          consists of members that are validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note that we instantiate the @('all-vals') input
     of @(tsee validator-committees-in-system-p)
     to the set of all validator addresses in the system state."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (validator-committees-in-system-p
                    (get-validator-state val systate)
                    (all-addresses systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committees-in-system-p-when-genesis
  :short "The invariant holds if
          the genesis committee's members are validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "We have already proved in @(tsee active-committee-at-round)
     that if that function calculates a committee from any blockchain,
     then the committee's members are validators in the system,
     so long as the genesis committee satisfies that property.
     So the invariant of interest holds
     under that condition on the genesis committee."))
  (implies (set::subset (committee-members (genesis-committee))
                        (all-addresses systate))
           (committees-in-system-p systate))
  :enable (committees-in-system-p
           validator-committees-in-system-p
           active-committee-at-round-subset-all-vals))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection genesis-committee-members-subset-invariant
  :short "Invariance of the condition on the genesis committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "To show that our invariant of interest, @(tsee committees-in-system-p),
     is indeed an invariant,
     given that we have proved @(tsee committees-in-system-p-when-genesis),
     it suffices to show that
     the condition on the genesis committee is itself an invariant.
     While the genesis committee does not change,
     the set of addresses @(tsee all-addresses) of validators in the system
     depends on the system state.
     But we have already proved that that set is an invariant,
     so it is easy to prove that it is preserved by transitions.
     Its establishment follows from the definition of @(tsee system-initp),
     which includes the condition that
     the genesis committee's members are validators in the system."))

  (defruled genesis-committee-members-subset-when-init
    (implies (system-initp systate)
             (set::subset (committee-members (genesis-committee))
                          (all-addresses systate)))
    :enable system-initp)

  (defruled genesis-committee-members-subset-of-next
    (implies (and (set::subset (committee-members (genesis-committee))
                               (all-addresses systate))
                  (event-possiblep event systate))
             (set::subset (committee-members (genesis-committee))
                          (all-addresses (event-next event systate))))))
