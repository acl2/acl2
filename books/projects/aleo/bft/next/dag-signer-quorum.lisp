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

(include-book "active-committees-after-commit")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dag-signer-quorum
  :parents (correctness)
  :short "Invariant that each certificate in the DAG of a validator
          has signers with a quorum stake."
  :long
  (xdoc::topstring
   (xdoc::p
    "Certificates are added to DAGs by @('certify') and @('accept') events.
     In both cases, the validator checks that
     the active committee for the certificate's round can be calculated,
     and that the signers' stake forms a quorum in that committee."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-signer-quorum-p ((systate system-statep))
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
                                     (>= (validators-stake
                                          (certificate->signers cert) commtt)
                                         (committee-quorum-stake commtt))))))))

  ///

  (fty::deffixequiv-sk dag-signer-quorum-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-signer-quorum-p-when-init
  :short "Establishment of the invariant in the initial states."
  (implies (system-initp systate)
           (dag-signer-quorum-p systate))
  :enable (dag-signer-quorum-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dag-signer-quorum-p-of-next
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
     @(see proposed-endorser-in-committee).")
   (xdoc::p
    "An @('accept') transition is simpler,
     because it explicitly checks that the signers are in the committee.")
   (xdoc::p
    "For @('commit'), since the blockchain is extended,
     we need to use @(tsee active-committee-at-round-of-commit-next)
     to show that the applicable committee does not change."))

  (defruled dag-signer-quorum-p-of-propose-next
    (implies (dag-signer-quorum-p systate)
             (dag-signer-quorum-p (propose-next prop dests systate)))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc))

  (defruled dag-signer-quorum-p-of-endorse-next
    (implies (dag-signer-quorum-p systate)
             (dag-signer-quorum-p (endorse-next prop endor systate)))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc))

  (defruled dag-signer-quorum-p-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (dag-signer-quorum-p systate))
             (dag-signer-quorum-p (augment-next prop endor systate)))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc))

  (defruled dag-signer-quorum-p-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (dag-signer-quorum-p systate))
             (dag-signer-quorum-p (certify-next cert dests systate)))
    :use ((:instance dag-signer-quorum-p-necc
                     (val (mv-nth 0 (dag-signer-quorum-p-witness
                                     (certify-next cert dests systate))))
                     (cert (mv-nth 1 (dag-signer-quorum-p-witness
                                      (certify-next cert dests systate))))))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc
             validator-state->dag-of-certify-next
             certify-possiblep
             certificate->author
             certificate->round
             certificate->signers
             omap::assoc-to-in-of-keys
             omap::lookup))

  (defruled dag-signer-quorum-p-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (dag-signer-quorum-p systate))
             (dag-signer-quorum-p (accept-next val cert systate)))
    :use (:instance dag-signer-quorum-p-necc
                    (val (mv-nth 0 (dag-signer-quorum-p-witness
                                    (accept-next val cert systate))))
                    (cert (mv-nth 1 (dag-signer-quorum-p-witness
                                     (accept-next val cert systate)))))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc
             accept-possiblep
             validator-state->dag-of-accept-next
             certificate->round))

  (defruled dag-signer-quorum-p-of-advance-next
    (implies (and (advance-possiblep val systate)
                  (dag-signer-quorum-p systate))
             (dag-signer-quorum-p (advance-next val systate)))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc))

  (defruled dag-signer-quorum-p-of-commit-next
    (implies (and (commit-possiblep val systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (dag-signer-quorum-p systate))
             (dag-signer-quorum-p (commit-next val systate)))
    :enable (dag-signer-quorum-p
             dag-signer-quorum-p-necc
             active-committee-at-round-of-commit-next))

  (defruled dag-signer-quorum-p-of-event-next
    (implies (and (event-possiblep event systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (dag-signer-quorum-p systate))
             (dag-signer-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-signer-quorum-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (dag-signer-quorum-p systate))
           (dag-signer-quorum-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-signer-quorum-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (dag-signer-quorum-p systate))
  :enable (system-state-reachablep
           dag-signer-quorum-p-when-init
           last-blockchain-round-p-when-init
           ordered-blockchain-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (last-blockchain-round-p from)
                   (ordered-blockchain-p from)
                   (dag-signer-quorum-p from))
              (dag-signer-quorum-p systate))
     :use (:instance
           dag-signer-quorum-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
