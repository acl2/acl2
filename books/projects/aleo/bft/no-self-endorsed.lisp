; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "reachability")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ no-self-endorsed
  :parents (correctness)
  :short "Invariant that the recorded author-round pairs
          of endorsed certificates are from other validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created,
     it is endorsed by validators other than the author of the certificate:
     @(tsee create-possiblep) checks that condition,
     and @(tsee create-next) extends the set of endorsed pairs
     of each endorser with the certificate's author and round.
     Thus, if the new set did not contain the validator's address,
     the new set does not contain it either.
     The other events
     either leave the set of endorsed pairs unchanged
     or remove pairs from it,
     thus preserving the absence of the validator's address in the set."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk no-self-endorsed-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          every pair in the endorsed set of a correct validator
          does not have the validator's address."
  :long
  (xdoc::topstring
   (xdoc::p
    "We express this by saying that
     retrieving, from the set of endorsed pairs of a validator,
     the ones with the validator's address
     yields the empty set."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (equal (address+pos-pairs-with-address
                           val
                           (validator-state->endorsed
                            (get-validator-state val systate)))
                          nil)))

  ///

  (fty::deffixequiv-sk no-self-endorsed-p
    :args ((systate system-statep)))

  (defruled no-self-endorsed-p-necc-fixing
    (implies (and (no-self-endorsed-p systate)
                  (set::in (address-fix val) (correct-addresses systate)))
             (equal (address+pos-pairs-with-address
                     val
                     (validator-state->endorsed
                      (get-validator-state val systate)))
                    nil))
    :use (:instance no-self-endorsed-p-necc (val (address-fix val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled no-self-endorsed-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "All the sets of endorsed pairs are initially empty,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (no-self-endorsed-p systate))
  :enable (no-self-endorsed-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection no-self-endorsed-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a certificate is created, a pair is added to all the endorsers,
     while the other validators keep the same set of endorsed pairs,
     and thus the invariant is preserved for them.
     So it remains to show that the newly added pair
     has an author distinct from any endorser.
     For the certificate to be created,
     @(tsee create-possiblep) must hold,
     which indirectly calls @(tsee create-signer-possiblep)
     for all the correct endorsers.
     As we are considering a generic correct endorser in the proof,
     we can use its @(tsee create-signer-possiblep)
     to show that the author is not the endorser,
     so the addition of the new pair preserves the invariant.")
   (xdoc::p
    "When a certificate is stored into the DAG,
     the validator removes, from the set of endorsed pairs,
     the pair with the certificate's author and round,
     if present in the set.
     So if the set satsfied the invariant before,
     it also does after the removal.
     The other validators keep the same set of endorsed pairs,
     so the invariant is preserved.")
   (xdoc::p
    "The other kinds of events do not change any set of endorsed pairs,
     and thus the invariant is preserved for all validators."))

  (defruled no-self-endorsed-p-of-create-next
    (implies (and (no-self-endorsed-p systate)
                  (create-possiblep cert systate))
             (no-self-endorsed-p (create-next cert systate)))
    :enable (no-self-endorsed-p
             no-self-endorsed-p-necc
             validator-state->endorsed-of-create-next
             address+pos-pairs-with-address-of-insert
             create-possiblep
             create-author-possiblep
             create-signer-possiblep))

  (defruled no-self-endorsed-p-of-accept-next
    (implies (and (no-self-endorsed-p systate)
                  (accept-possiblep msg systate))
             (no-self-endorsed-p (accept-next msg systate)))
    :enable (no-self-endorsed-p
             no-self-endorsed-p-necc
             validator-state->endorsed-of-accept-next
             address+pos-pairs-with-address-of-delete))

  (defruled no-self-endorsed-p-of-advance-next
    (implies (and (no-self-endorsed-p systate)
                  (advance-possiblep val systate))
             (no-self-endorsed-p (advance-next val systate)))
    :enable (no-self-endorsed-p
             no-self-endorsed-p-necc))

  (defruled no-self-endorsed-p-of-commit-next
    (implies (and (no-self-endorsed-p systate)
                  (commit-possiblep val systate))
             (no-self-endorsed-p (commit-next val systate)))
    :enable (no-self-endorsed-p
             no-self-endorsed-p-necc))

  (defruled no-self-endorsed-p-of-event-next
    (implies (and (no-self-endorsed-p systate)
                  (event-possiblep event systate))
             (no-self-endorsed-p (event-next event systate)))
    :enable (event-next
             event-possiblep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled no-self-endorsed-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (no-self-endorsed-p systate))
           (no-self-endorsed-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled no-self-endorsed-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (no-self-endorsed-p systate))
  :enable (system-state-reachablep
           no-self-endorsed-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (no-self-endorsed-p from))
              (no-self-endorsed-p systate))
     :use (:instance
           no-self-endorsed-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
