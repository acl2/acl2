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

(include-book "omni-paths-def-and-implied")
(include-book "anchors-extension")

(local (include-book "library-extensions/arithmetic-theorems"))

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committed-anchor-sequences
  :parents (correctness)
  :short "Sequences of anchors committed by validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an operation to collect
     all the anchors committed by a validator so far,
     and we prove properties of it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committed-anchors ((vstate validator-statep))
  :guard (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate)))
  :returns (anchors certificate-listp)
  :short "Sequence of anchors committed by a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the last committed round is 0 (i.e. there is no last committed round),
     no anchors have been committed, and we return @('nil').
     Otherwise, we obtain the last committed anchor,
     and we use @(tsee collect-all-anchors) starting from that one.
     Thus, this function gives us the list of all anchors committed so far,
     in reverse chronological order
     (i.e. the latest one is the @(tsee car) of the list)."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) nil)
       (last-anchor (last-anchor vstate)))
    (collect-all-anchors last-anchor vstate.dag vstate.blockchain))
  :guard-hints
  (("Goal" :in-theory (enable last-anchor-in-dag
                              active-committee-at-round-when-last-anchor
                              certificate->round-of-last-anchor)))
  :hooks (:fix)

  ///

  (defruled committed-anchors-when-last-is-0
    (implies (equal (validator-state->last vstate) 0)
             (equal (committed-anchors vstate)
                    nil)))

  (defrule consp-of-committed-anchors-when-last-not-0
    (implies (not (equal (validator-state->last vstate) 0))
             (consp (committed-anchors vstate)))
    :rule-classes :type-prescription)

  (defruled car-of-committed-anchors
    (implies (and (not (equal (validator-state->last vstate) 0))
                  (last-anchor vstate))
             (equal (car (committed-anchors vstate))
                    (last-anchor vstate)))
    :enable car-of-collect-all-anchors)

  (defret certificate-list-evenp-of-committed-anchors
    (certificate-list-evenp anchors)
    :hyp (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate)))
    :hints (("Goal" :in-theory (enable certificate->round-of-last-anchor))))

  (defret certificate-list-orderedp-of-committed-anchors
    (certificate-list-orderedp anchors)
    :hyp (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate)))
    :hints
    (("Goal"
      :in-theory (enable certificate-list-orderedp-of-collect-all-anchors
                         certificate->round-of-last-anchor))))
  (in-theory (disable certificate-list-orderedp-of-committed-anchors))

  (defret certificates-dag-paths-p-of-committed-anchors
    (certificates-dag-paths-p anchors (validator-state->dag vstate))
    :hyp (or (equal (validator-state->last vstate) 0)
             (set::in (last-anchor vstate)
                      (validator-state->dag vstate)))
    :hints
    (("Goal"
      :in-theory (enable certificates-dag-paths-p-of-nil
                         certificates-dag-paths-p-of-collect-all-anchors))))
  (in-theory (disable certificates-dag-paths-p-of-committed-anchors)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-when-init
  :short "Initially, a validator has no committed anchors."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (committed-anchors (get-validator-state val systate))
                  nil))
  :enable (committed-anchors
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection committed-anchors-of-next
  :short "How the sequence of committed anchors in a validator state
          changes (or not) for each transition."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create') or @('accept') event
     does not change the last committed anchor or the blockchain,
     but it extends the DAG.
     However, given that @(tsee collect-all-anchors)
     is stable under DAG extension as already proved
     in @('collect-all-anchors-of-unequivocal-superdag'),
     there is no change to the sequence of committed anchors.
     To discharge the hypothesis of that theorem,
     saying that the extended DAG is unequivocal,
     we use the already proved theorem that
     DAG non-equivocation is preserved by these events.")
   (xdoc::p
    "A @('commit') event is the only kind
     that changes the sequence of committed anchors
     (for the target validator),
     by extending them with a suitable call of @(tsee collect-anchors).
     The proof takes a little work.
     We distinguish the case of the target validator
     from the case of another validator (which is easy),
     and within the first case we consider two sub-cases
     based on whether the last committed round was 0 or not.
     The case in which it is 0 is relatively simple,
     because the second argument of the @(tsee append) is @('nil'),
     since no anchors have been committed yet;
     we open @(tsee collect-all-anchors),
     and we need to simplify away the blockchain extension
     via the theorem @('collect-anchors-of-extend-blockchain-no-change'),
     which involved other rules to relieve its hypotheses.
     The sub-cases in which there are already some committed anchors
     is the more complex;
     the most important theorem used there is
     @(tsee collect-all-anchors-to-append-of-collect-anchors),
     and again we need rules to simplify away the blockchain extension.
     In both sub-cases, the blockchain extension arises
     from the definition of @(tsee committed-anchors).")
   (xdoc::p
    "An @('advance') event does not modify
     the DAG or the blockchain or the last committed round or the last anchor,
     and thus it is easy to prove that
     the sequence of committed anchors does not change."))

  ;; create:

  (defrule committed-anchors-of-create-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (create-possiblep cert systate))
             (equal (committed-anchors
                     (get-validator-state val (create-next cert systate)))
                    (committed-anchors
                     (get-validator-state val systate))))
    :enable (committed-anchors
             validator-state->dag-of-create-next
             backward-closed-p-necc
             last-anchor-present-p-necc
             last-anchor-in-dag)
    :use ((:instance collect-all-anchors-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state
                             (certificate->author cert) systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            (create-next cert systate))))
                     (blockchain (validator-state->blockchain
                                  (get-validator-state
                                   (certificate->author cert)
                                   (create-next cert systate))))
                     (last-anchor (last-anchor
                                   (get-validator-state
                                    (certificate->author cert) systate))))
          (:instance unequivocal-dags-p-necc-single
                     (val (certificate->author cert))
                     (systate (create-next cert systate)))))

  ;; accept:

  (defrule committed-anchors-of-accept-next
    (implies (and (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (set::in val (correct-addresses systate))
                  (accept-possiblep msg systate)
                  (messagep msg))
             (equal (committed-anchors
                     (get-validator-state val (accept-next msg systate)))
                    (committed-anchors
                     (get-validator-state val systate))))
    :enable (accept-possiblep
             committed-anchors
             validator-state->dag-of-accept-next
             backward-closed-p-necc
             last-anchor-present-p-necc
             last-anchor-in-dag
             unequivocal-dags-p-of-accept-next)
    :use ((:instance collect-all-anchors-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state (message->destination msg)
                                                 systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (message->destination msg)
                            (accept-next msg systate))))
                     (blockchain (validator-state->blockchain
                                  (get-validator-state
                                   (message->destination msg)
                                   (accept-next msg systate))))
                     (last-anchor (last-anchor
                                   (get-validator-state
                                    (message->destination msg) systate))))
          (:instance unequivocal-dags-p-necc-single
                     (val (message->destination msg))
                     (systate (accept-next msg systate)))))

  ;; advance:

  (defrule committed-anchors-of-advance-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-possiblep val1 systate))
             (equal (committed-anchors
                     (get-validator-state val (advance-next val1 systate)))
                    (committed-anchors
                     (get-validator-state val systate))))
    :enable committed-anchors)

  ;; commit:

  (defruled committed-anchors-of-commit-next-last-not-0
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val systate)
                  (not (equal (validator-state->last
                               (get-validator-state val systate))
                              0)))
             (equal (committed-anchors
                     (get-validator-state val (commit-next val systate)))
                    (b* (((validator-state vstate)
                          (get-validator-state val systate))
                         (round (1- vstate.round))
                         (commtt (active-committee-at-round
                                  round vstate.blockchain))
                         (leader (leader-at-round round commtt))
                         (anchor (cert-with-author+round
                                  leader round vstate.dag))
                         (anchors (collect-anchors anchor
                                                   (- round 2)
                                                   vstate.last
                                                   vstate.dag
                                                   vstate.blockchain)))
                      (append anchors
                              (committed-anchors
                               (get-validator-state val systate))))))
    :enable (committed-anchors
             validator-state->last-of-commit-next
             validator-state->blockchain-of-commit-next
             last-anchor-of-commit-next
             collect-all-anchors-of-extend-blockchain-no-change
             blocks-orderedp-of-extend-blockchain
             certificate-list-orderedp-of-collect-anchors
             commit-possiblep
             evenp-of-1-less-when-not-evenp
             evenp-of-3-less-when-not-evenp
             active-committee-at-previous-round-when-at-round
             posp
             ordered-blockchain-p-necc
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc
             dag-has-committees-p-when-signer-quorum-p
             dag-in-committees-p-when-signer-quorum-p
             last-anchor-present-p-necc
             last-anchor-in-dag
             certificate->round-of-last-anchor
             certificate->author-of-last-anchor
             omni-paths-p-necc
             cert-with-author+round-element)
    :use (:instance collect-all-anchors-to-append-of-collect-anchors
                    (anchor (last-anchor (get-validator-state val systate)))
                    (anchor1 (cert-with-author+round
                              (leader-at-round
                               (1- (validator-state->round
                                    (get-validator-state val systate)))
                               (active-committee-at-round
                                (1- (validator-state->round
                                     (get-validator-state val systate)))
                                (validator-state->blockchain
                                 (get-validator-state val systate))))
                              (1- (validator-state->round
                                   (get-validator-state val systate)))
                              (validator-state->dag
                               (get-validator-state val systate))))
                    (dag (validator-state->dag
                          (get-validator-state val systate)))
                    (blockchain (validator-state->blockchain
                                 (get-validator-state val systate)))))

  (defruled committed-anchors-of-commit-next-last-0
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-possiblep val systate)
                  (equal (validator-state->last
                          (get-validator-state val systate))
                         0))
             (equal (committed-anchors
                     (get-validator-state val (commit-next val systate)))
                    (b* (((validator-state vstate)
                          (get-validator-state val systate))
                         (round (1- vstate.round))
                         (commtt (active-committee-at-round
                                  round vstate.blockchain))
                         (leader (leader-at-round round commtt))
                         (anchor (cert-with-author+round leader
                                                         round
                                                         vstate.dag))
                         (anchors (collect-anchors anchor
                                                   (- round 2)
                                                   vstate.last
                                                   vstate.dag
                                                   vstate.blockchain)))
                      (append anchors
                              (committed-anchors
                               (get-validator-state val systate))))))
    :enable (committed-anchors
             validator-state->last-of-commit-next
             validator-state->blockchain-of-commit-next
             last-anchor-of-commit-next
             commit-possiblep
             collect-all-anchors
             pos-fix
             collect-anchors-of-extend-blockchain-no-change
             ordered-blockchain-p-necc
             blocks-orderedp-of-extend-blockchain
             certificate-list-orderedp-of-collect-anchors
             evenp
             posp
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc
             active-committee-at-previous3-round-when-at-round))

  (defruled committed-anchors-of-commit-next-other-val
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val1 (correct-addresses systate))
                  (commit-possiblep val systate)
                  (addressp val)
                  (not (equal val1 val)))
             (equal (committed-anchors
                     (get-validator-state val1 (commit-next val systate)))
                    (committed-anchors
                     (get-validator-state val1 systate))))
    :enable (committed-anchors
             validator-state->last-of-commit-next
             validator-state->blockchain-of-commit-next
             last-anchor-of-commit-next))

  (defruled committed-anchors-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (set::in val1 (correct-addresses systate))
                  (commit-possiblep val systate)
                  (addressp val))
             (equal (committed-anchors
                     (get-validator-state val1 (commit-next val systate)))
                    (if (equal val1 (address-fix val))
                        (b* (((validator-state vstate)
                              (get-validator-state val1 systate))
                             (round (1- vstate.round))
                             (commtt (active-committee-at-round
                                      round vstate.blockchain))
                             (leader (leader-at-round round commtt))
                             (anchor (cert-with-author+round
                                      leader
                                      round
                                      vstate.dag))
                             (anchors (collect-anchors
                                       anchor
                                       (- round 2)
                                       vstate.last
                                       vstate.dag
                                       vstate.blockchain)))
                          (append anchors
                                  (committed-anchors
                                   (get-validator-state val1 systate))))
                      (committed-anchors
                       (get-validator-state val1 systate)))))
    :use (committed-anchors-of-commit-next-last-not-0
          committed-anchors-of-commit-next-last-0
          committed-anchors-of-commit-next-other-val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-commit-next-to-collect-all-anchors
  :short "Rewriting of @(tsee committed-anchors) after @('commit')
          to @(tsee collect-all-anchors) on the old system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "While the theorem @('committed-anchors-of-commit-next')
     in @(see committed-anchors-of-next)
     expresses the new committed anchor sequence in terms of the old one,
     specifically as the @(tsee append) of the new anchors to the old ones,
     this theorem provides a different expression for
     the committed anchor sequence after a @('commit') event.
     This is only for the target validator, the one that commits new anchors.
     The right side of this rewrite rule is
     a call of @(tsee collect-all-anchors)
     solely in terms of the old system state.
     This is used for certain proofs, elsewhere.")
   (xdoc::p
    "The main issue in this proof is to eliminate the extended blockchain,
     since @(tsee committed-anchors) on the new state
     makes use of the new blockchain.
     However, as also proved elsewhere, the addition to the blockchain
     does not affect the computation of the committees,
     and thus of the anchor sequence."))
  (implies (and (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (signer-quorum-p systate)
                (unequivocal-dags-p systate)
                (last-anchor-present-p systate)
                (omni-paths-p systate)
                (commit-possiblep val systate)
                (addressp val))
           (equal (committed-anchors
                   (get-validator-state val (commit-next val systate)))
                  (b* (((validator-state vstate)
                        (get-validator-state val systate))
                       (round (1- vstate.round)))
                    (collect-all-anchors
                     (cert-with-author+round
                      (leader-at-round round
                                       (active-committee-at-round
                                        round vstate.blockchain))
                      round
                      vstate.dag)
                     vstate.dag
                     vstate.blockchain))))
  :enable (commit-possiblep
           committed-anchors
           validator-state->last-of-commit-next
           validator-state->blockchain-of-commit-next
           validator-state->dag-of-commit-next
           last-anchor-of-commit-next
           collect-all-anchors-of-extend-blockchain-no-change
           ordered-blockchain-p-necc
           blocks-orderedp-of-extend-blockchain
           certificate-list-orderedp-of-collect-anchors
           certificate->round-of-cert-with-author+round
           evenp-of-1-less-when-not-evenp
           evenp-of-3-less-when-not-evenp
           posp
           last-blockchain-round-p-necc
           collect-anchors-above-last-committed-round
           active-committee-at-previous-round-when-at-round))
