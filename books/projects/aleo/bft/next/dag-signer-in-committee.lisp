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

(include-book "proposed-author-in-committee")
(include-book "proposed-endorser-in-committee")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dag-signer-in-committee
  :parents (correctness)
  :short "Invariant that each signer of each certificate in a DAG is
          in the active committee at the round of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certificates are added to DAGs by @('certify') and @('accept') events.")
   (xdoc::p
    "A @('certify') event creates the certificate from a pending proposal,
     whose author and endorsers are in the committee,
     as proved in @(see proposed-author-in-committee)
     and @(see proposed-endorser-in-committee).")
   (xdoc::p
    "In an @('accept') event, the accepting validator
     explicitly checks that the signers are in the committee."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-signer-in-committee-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant."
  (forall (val cert)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (implies (set::in cert vstate.dag)
                              (b* ((commtt (active-committee-at-round
                                            (certificate->round cert)
                                            vstate.blockchain)))
                                (and commtt
                                     (set::subset
                                      (certificate->signers cert)
                                      (committee-members commtt))))))))

  ///

  (fty::deffixequiv-sk dag-signer-in-committee-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-signer-in-committee-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (dag-signer-in-committee-p systate))
  :enable (dag-signer-in-committee-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dag-signer-in-committee-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that may change the DAG
     are @('certify') and @('accept').")
   (xdoc::p
    "A @('certify') transition happens only if
     the validator can calculate the committee.
     Although @(tsee certify-possiblep) does not explicitly check
     that author and endorsers are members of the committee,
     it is an invariant that they are, as proved in
     @(see proposed-author-in-committee) and
     @(see proposed-endorser-in-committee).")
   (xdoc::p
    "An @('accept') transition is simpler,
     because it explicitly checks that the signers are in the committee.")
   (xdoc::p
    "For @('commit'), since the blockchain is extended,
     we need to use @(tsee active-committee-at-round-of-commit-next)
     to show that the applicable committee does not change."))

  (defruled dag-signer-in-committee-p-of-propose-next
    (implies (dag-signer-in-committee-p systate)
             (dag-signer-in-committee-p (propose-next prop dests systate)))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc))

  (defruled dag-signer-in-committee-p-of-endorse-next
    (implies (dag-signer-in-committee-p systate)
             (dag-signer-in-committee-p (endorse-next prop endor systate)))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc))

  (defruled dag-signer-in-committee-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (dag-signer-in-committee-p systate))
             (dag-signer-in-committee-p (augment-next prop endor systate)))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc))

  (defruled dag-signer-in-committee-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-author-in-committee-p systate)
                  (proposed-endorser-in-committee-p systate)
                  (dag-signer-in-committee-p systate))
             (dag-signer-in-committee-p (certify-next cert dests systate)))
    :use ((:instance dag-signer-in-committee-p-necc
                     (val (mv-nth 0 (dag-signer-in-committee-p-witness
                                     (certify-next cert dests systate))))
                     (cert (mv-nth 1 (dag-signer-in-committee-p-witness
                                      (certify-next cert dests systate)))))
          (:instance proposed-endorser-in-committee-p-necc
                     (val (mv-nth 0 (dag-signer-in-committee-p-witness
                                     (certify-next cert dests systate))))
                     (prop (certificate->proposal cert))))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc
             proposed-author-in-committee-p-necc
             validator-state->dag-of-certify-next
             certify-possiblep
             certificate->author
             certificate->round
             certificate->signers
             omap::assoc-to-in-of-keys
             omap::lookup))

  (defruled dag-signer-in-committee-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (dag-signer-in-committee-p systate))
             (dag-signer-in-committee-p (accept-next val cert systate)))
    :use (:instance dag-signer-in-committee-p-necc
                    (val (mv-nth 0 (dag-signer-in-committee-p-witness
                                    (accept-next val cert systate))))
                    (cert (mv-nth 1 (dag-signer-in-committee-p-witness
                                     (accept-next val cert systate)))))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc
             accept-possiblep
             validator-state->dag-of-accept-next
             certificate->round))

  (defruled dag-signer-in-committee-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (dag-signer-in-committee-p systate))
             (dag-signer-in-committee-p (advance-next val systate)))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc))

  (defruled dag-signer-in-committee-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (dag-signer-in-committee-p systate))
             (dag-signer-in-committee-p (commit-next val systate)))
    :enable (dag-signer-in-committee-p
             dag-signer-in-committee-p-necc
             active-committee-at-round-of-commit-next))

  (defruled dag-signer-in-committee-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (proposed-author-in-committee-p systate)
                  (proposed-endorser-in-committee-p systate)
                  (dag-signer-in-committee-p systate))
             (dag-signer-in-committee-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-signer-in-committee-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (proposed-author-in-committee-p systate)
                (proposed-endorser-in-committee-p systate)
                (dag-signer-in-committee-p systate))
           (dag-signer-in-committee-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-signer-in-committee-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (dag-signer-in-committee-p systate))
  :enable (system-state-reachablep
           dag-signer-in-committee-p-when-init
           last-blockchain-round-p-when-init
           ordered-blockchain-p-when-init
           proposed-author-in-committee-p-when-init
           proposed-endorser-in-committee-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-blockchain-p from)
                   (proposed-author-in-committee-p from)
                   (proposed-endorser-in-committee-p from)
                   (dag-signer-in-committee-p from))
              (dag-signer-in-committee-p systate))
     :use (:instance
           dag-signer-in-committee-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
