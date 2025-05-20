; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "proposed-author-in-committee")
(include-book "proposed-endorser-in-committee")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signer-quorum
  :parents (correctness)
  :short "Invariant that each certificate in the DAG of a validator
          has signers that form a quorum in the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certificates are added to DAGs by @('certify') and @('accept') events.
     In both cases, the validator checks that
     the active committee for the certificate's round can be calculated,
     and that the signers form a quorum in that committee."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signer-quorum-p ((systate system-statep))
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
                                     (set::subset (certificate->signers cert)
                                                  (committee-members commtt))
                                     (>= (committee-members-stake
                                          (certificate->signers cert) commtt)
                                         (committee-quorum-stake commtt))))))))

  ///

  (fty::deffixequiv-sk signer-quorum-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-quorum-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (signer-quorum-p systate))
  :enable (signer-quorum-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signer-quorum-p-of-next
  :short "Preservation of the invariant by single transitions."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only two kinds of events that may change the DAG
     are @('certify') and @('accept').")
   (xdoc::p
    "A @('certify') transition happens only if
     the validator can calculate the committee
     and the stake of the author and endorsers meets the quorum stake.
     Although @(tsee certify-possiblep) does not explicitly check
     that author and endorsers are members of the committee,
     it is an invariant that they are, as proved in
     @(see proposed-author-in-committee) and
     @(see proposed-endorser-in-committee).
     Another slight difference is that
     @(tsee certify-possiblep) uses @(tsee committee-validators-stake),
     while the invariant uses @(tsee committee-members-stake);
     but since author and endorsers are in the committee,
     the two are equal, as proved in @(tsee committee-validators-stake).")
   (xdoc::p
    "An @('accept') transition is simpler,
     because it explicitly checks that the signers are in the committee
     and it uses @(tsee committee-members-stake).")
   (xdoc::p
    "For @('commit'), since the blockchain is extended,
     we need to use @(tsee active-committee-at-round-of-commit-next)
     to show that the applicable committee does not change."))

  (defruled signer-quorum-p-of-propose-next
    (implies (signer-quorum-p systate)
             (signer-quorum-p (propose-next prop dests systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc))

  (defruled signer-quorum-p-of-endorse-next
    (implies (signer-quorum-p systate)
             (signer-quorum-p (endorse-next prop endor systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc))

  (defruled signer-quorum-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (signer-quorum-p systate))
             (signer-quorum-p (augment-next prop endor systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc))

  (defruled signer-quorum-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (proposed-author-in-committee-p systate)
                  (proposed-endorser-in-committee-p systate)
                  (signer-quorum-p systate))
             (signer-quorum-p (certify-next cert dests systate)))
    :use ((:instance signer-quorum-p-necc
                     (val (mv-nth 0 (signer-quorum-p-witness
                                     (certify-next cert dests systate))))
                     (cert (mv-nth 1 (signer-quorum-p-witness
                                      (certify-next cert dests systate)))))
          (:instance proposed-endorser-in-committee-p-necc
                     (val (mv-nth 0 (signer-quorum-p-witness
                                     (certify-next cert dests systate))))
                     (prop (certificate->proposal cert))))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             proposed-author-in-committee-p-necc
             validator-state->dag-of-certify-next
             certify-possiblep
             certificate->author
             certificate->round
             committee-validators-stake-to-committee-members-stake
             certificate->signers
             omap::assoc-to-in-of-keys
             omap::lookup))

  (defruled signer-quorum-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (signer-quorum-p systate))
             (signer-quorum-p (accept-next val cert systate)))
    :expand (signer-quorum-p (accept-next val cert systate))
    :use (:instance signer-quorum-p-necc
                    (val (mv-nth 0 (signer-quorum-p-witness
                                    (accept-next val cert systate))))
                    (cert (mv-nth 1 (signer-quorum-p-witness
                                     (accept-next val cert systate)))))
    :enable (signer-quorum-p-necc
             accept-possiblep
             validator-state->dag-of-accept-next
             certificate->round))

  (defruled signer-quorum-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (signer-quorum-p systate))
             (signer-quorum-p (advance-next val systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc))

  (defruled signer-quorum-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate))
             (signer-quorum-p (commit-next val systate)))
    :enable (signer-quorum-p
             signer-quorum-p-necc
             active-committee-at-round-of-commit-next))

  (defruled signer-quorum-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (proposed-author-in-committee-p systate)
                  (proposed-endorser-in-committee-p systate)
                  (signer-quorum-p systate))
             (signer-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-quorum-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (proposed-author-in-committee-p systate)
                (proposed-endorser-in-committee-p systate)
                (signer-quorum-p systate))
           (signer-quorum-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-quorum-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (signer-quorum-p systate))
  :enable (system-state-reachablep
           signer-quorum-p-when-init
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
                   (signer-quorum-p from))
              (signer-quorum-p systate))
     :use (:instance
           signer-quorum-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
