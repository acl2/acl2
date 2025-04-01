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

(include-book "omni-paths-def-and-implied")
(include-book "anchors-extension")

(local (include-book "../library-extensions/arithmetic-theorems"))

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committed-anchors-sequences
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

(define committed-anchors ((vstate validator-statep) (all-vals address-setp))
  :guard (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate all-vals)))
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
       (last-anchor (last-anchor vstate all-vals)))
    (collect-all-anchors last-anchor vstate.dag vstate.blockchain all-vals))
  :guard-hints
  (("Goal" :in-theory (enable last-anchor-in-dag
                              active-committee-at-round-when-last-anchor
                              certificate->round-of-last-anchor)))

  ///

  (defruled committed-anchors-when-last-is-0
    (implies (equal (validator-state->last vstate) 0)
             (equal (committed-anchors vstate all-vals)
                    nil)))

  (defrule consp-of-committed-anchors-when-last-not-0
    (implies (not (equal (validator-state->last vstate) 0))
             (consp (committed-anchors vstate all-vals)))
    :rule-classes :type-prescription)

  (defruled car-of-committed-anchors
    (implies (and (not (equal (validator-state->last vstate) 0))
                  (last-anchor vstate all-vals))
             (equal (car (committed-anchors vstate all-vals))
                    (last-anchor vstate all-vals)))
    :enable car-of-collect-all-anchors)

  (defret certificates-dag-paths-p-of-committed-anchors
    (certificates-dag-paths-p anchors (validator-state->dag vstate))
    :hyp (or (equal (validator-state->last vstate) 0)
             (set::in (last-anchor vstate all-vals)
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
           (equal (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))
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
    "A @('create-certificate') or @('store-certificate') event
     does not change the last committed anchor or the blockchain,
     but it extends the DAG.
     However, given that @(tsee collect-all-anchors)
     is stable under DAG extension as already proved
     in @('collect-all-anchors-of-unequivocal-superdag'),
     there is no change to the sequence of committed anchors.
     To discharge the hypothesis of that theorem,
     saying that the extended DAG is unequivocal,
     we use the already proved theorem that
     DAG non-equivocation is preserved by these events.
     Interestingly, ACL2's tau can use those theorems,
     namely @('unequivocal-accepted-certificates-p-of-create-certificate-next')
     and @('unequivocal-accepted-certificates-p-of-store-certificate-next')
     automatically,
     but for more explicitness in the proof,
     we disable tau and enable those theorems.")
   (xdoc::p
    "A @('commit-anchors') event is the only kind
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
    "The other three kinds of events do not modify
     the DAG or the blockchain or the last committed round or the last anchor,
     and thus it is easy to prove that
     the sequence of committed anchors does not change."))

  ;; create-certificate:

  (defruled committed-anchors-of-create-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (backward-closed-p systate)
                  (set::in val (correct-addresses systate))
                  (create-certificate-possiblep cert systate))
             (equal (committed-anchors
                     (get-validator-state
                      val (create-certificate-next cert systate))
                     (all-addresses systate))
                    (committed-anchors
                     (get-validator-state val systate)
                     (all-addresses systate))))
    :disable ((:e tau-system))
    :enable (committed-anchors
             last-anchor-of-create-certificate-next
             validator-state->last-of-create-certificate-next
             validator-state->dag-of-create-certificate-next
             validator-state->blockchain-of-create-certificate-next
             backward-closed-p-necc
             last-anchor-present-p-necc
             last-anchor-in-dag
             unequivocal-accepted-certificates-p-of-create-certificate-next)
    :use ((:instance collect-all-anchors-of-unequivocal-superdag
                     (dag0 (validator-state->dag
                            (get-validator-state
                             (certificate->author cert) systate)))
                     (dag (validator-state->dag
                           (get-validator-state
                            (certificate->author cert)
                            (create-certificate-next cert systate))))
                     (blockchain (validator-state->blockchain
                                  (get-validator-state
                                   (certificate->author cert)
                                   (create-certificate-next cert systate))))
                     (last-anchor (last-anchor
                                   (get-validator-state
                                    (certificate->author cert) systate)
                                   (all-addresses systate)))
                     (all-vals (all-addresses systate)))
          (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                     (val (certificate->author cert))
                     (systate (create-certificate-next cert systate)))))

  ;; receive certificate:

  (defruled committed-anchors-of-receive-certificate-next
    (implies (and (set::in val (correct-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (equal (committed-anchors
                     (get-validator-state
                      val (receive-certificate-next msg systate))
                     (all-addresses systate))
                    (committed-anchors
                     (get-validator-state val systate)
                     (all-addresses systate))))
    :enable (committed-anchors
             last-anchor-of-receive-certificate-next
             validator-state->last-of-receive-certificate-next
             validator-state->blockchain-of-receive-certificate-next
             validator-state->dag-of-receive-certificate-next))

  ;; store-certificate:

  (defruled committed-anchors-of-store-certificate-next
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (signer-records-p systate)
                  (committees-in-system-p systate)
                  (system-fault-tolerant-p systate)
                  (signer-quorum-p systate)
                  (same-committees-p systate)
                  (no-self-buffer-p systate)
                  (no-self-endorsed-p systate)
                  (same-owned-certificates-p systate)
                  (accepted-certificate-committee-p systate)
                  (last-anchor-present-p systate)
                  (backward-closed-p systate)
                  (set::in val (correct-addresses systate))
                  (store-certificate-possiblep val1 cert systate))
             (equal (committed-anchors
                     (get-validator-state
                      val (store-certificate-next val1 cert systate))
                     (all-addresses systate))
                    (committed-anchors
                     (get-validator-state val systate)
                     (all-addresses systate))))
    :use (:instance lemma (val1 (address-fix val1)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (unequivocal-accepted-certificates-p systate)
                     (signer-records-p systate)
                     (committees-in-system-p systate)
                     (system-fault-tolerant-p systate)
                     (signer-quorum-p systate)
                     (same-committees-p systate)
                     (no-self-buffer-p systate)
                     (no-self-endorsed-p systate)
                     (same-owned-certificates-p systate)
                     (accepted-certificate-committee-p systate)
                     (last-anchor-present-p systate)
                     (backward-closed-p systate)
                     (set::in val (correct-addresses systate))
                     (store-certificate-possiblep val1 cert systate)
                     (addressp val1))
                (equal (committed-anchors
                        (get-validator-state
                         val (store-certificate-next val1 cert systate))
                        (all-addresses systate))
                       (committed-anchors (get-validator-state val systate)
                                          (all-addresses systate))))
       :disable ((:e tau-system))
       :enable (store-certificate-possiblep
                committed-anchors
                last-anchor-of-store-certificate-next
                validator-state->last-of-store-certificate-next
                validator-state->dag-of-store-certificate-next
                validator-state->blockchain-of-store-certificate-next
                backward-closed-p-necc
                last-anchor-present-p-necc
                last-anchor-in-dag
                unequivocal-accepted-certificates-p-of-store-certificate-next)
       :use ((:instance collect-all-anchors-of-unequivocal-superdag
                        (dag0 (validator-state->dag
                               (get-validator-state val1 systate)))
                        (dag (validator-state->dag
                              (get-validator-state
                               val1 (store-certificate-next
                                     val1 cert systate))))
                        (blockchain (validator-state->blockchain
                                     (get-validator-state
                                      val1
                                      (store-certificate-next
                                       val1 cert systate))))
                        (last-anchor (last-anchor
                                      (get-validator-state
                                       val1 systate)
                                      (all-addresses systate)))
                        (all-vals (all-addresses systate)))
             (:instance certificate-set-unequivocalp-when-unequivocal-accepted
                        (val val1)
                        (systate
                         (store-certificate-next val1 cert systate)))))))

  ;; advance-round:

  (defruled committed-anchors-of-advance-round-next
    (implies (and (set::in val (correct-addresses systate))
                  (advance-round-possiblep val1 systate))
             (equal (committed-anchors
                     (get-validator-state
                      val (advance-round-next val1 systate))
                     (all-addresses systate))
                    (committed-anchors
                     (get-validator-state val systate)
                     (all-addresses systate))))
    :enable (committed-anchors
             last-anchor-of-advance-round-next
             validator-state->last-of-advance-round-next
             validator-state->blockchain-of-advance-round-next
             validator-state->dag-of-advance-round-next))

  ;; commit-anchors:

  (defruled committed-anchors-of-commit-anchors-next-last-not-0
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val systate)
                  (not (equal (validator-state->last
                               (get-validator-state val systate))
                              0)))
             (equal (committed-anchors
                     (get-validator-state
                      val (commit-anchors-next val systate))
                     (all-addresses systate))
                    (b* (((validator-state vstate)
                          (get-validator-state val systate))
                         (round (1- vstate.round))
                         (commtt (active-committee-at-round
                                  round
                                  vstate.blockchain
                                  (all-addresses systate)))
                         (leader (leader-at-round round commtt))
                         (anchor (cert-with-author+round leader
                                                                round
                                                                vstate.dag))
                         (anchors (collect-anchors anchor
                                                   (- round 2)
                                                   vstate.last
                                                   vstate.dag
                                                   vstate.blockchain
                                                   (all-addresses systate))))
                      (append anchors
                              (committed-anchors
                               (get-validator-state val systate)
                               (all-addresses systate))))))
    :enable (committed-anchors
             validator-state->last-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             validator-state->dag-of-commit-anchors-next
             last-anchor-of-commit-anchors-next
             collect-all-anchors-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             certificate->round-of-cert-with-author+round
             commit-anchors-possiblep
             aleobft::evenp-of-1-less-when-not-evenp
             aleobft::evenp-of-3-less-when-not-evenp
             active-committee-at-previous-round-when-at-round
             evenp-of-blocks-last-round
             pos-fix
             posp
             ordered-even-p-necc
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc
             dag-committees-p-when-accepted-certificate-committee-p
             last-anchor-present-p-necc
             last-anchor-in-dag
             certificate->round-of-last-anchor
             certificate->author-of-last-anchor
             omni-paths-p-necc
             cert-with-author+round-element)
    :use (:instance collect-all-anchors-to-append-of-collect-anchors
                    (anchor (last-anchor (get-validator-state val systate)
                                         (all-addresses systate)))
                    (anchor1 (cert-with-author+round
                              (leader-at-round
                               (1- (validator-state->round
                                    (get-validator-state val systate)))
                               (active-committee-at-round
                                (1- (validator-state->round
                                     (get-validator-state val systate)))
                                (validator-state->blockchain
                                 (get-validator-state val systate))
                                (all-addresses systate)))
                              (1- (validator-state->round
                                   (get-validator-state val systate)))
                              (validator-state->dag
                               (get-validator-state val systate))))
                    (dag (validator-state->dag
                          (get-validator-state val systate)))
                    (blockchain (validator-state->blockchain
                                 (get-validator-state val systate)))
                    (all-vals (all-addresses systate))))

  (defruled committed-anchors-of-commit-anchors-next-last-0
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val (correct-addresses systate))
                  (commit-anchors-possiblep val systate)
                  (equal (validator-state->last
                          (get-validator-state val systate))
                         0))
             (equal (committed-anchors
                     (get-validator-state
                      val (commit-anchors-next val systate))
                     (all-addresses systate))
                    (b* (((validator-state vstate)
                          (get-validator-state val systate))
                         (round (1- vstate.round))
                         (commtt (active-committee-at-round
                                  round
                                  vstate.blockchain
                                  (all-addresses systate)))
                         (leader (leader-at-round round commtt))
                         (anchor (cert-with-author+round leader
                                                                round
                                                                vstate.dag))
                         (anchors (collect-anchors anchor
                                                   (- round 2)
                                                   vstate.last
                                                   vstate.dag
                                                   vstate.blockchain
                                                   (all-addresses systate))))
                      (append anchors
                              (committed-anchors
                               (get-validator-state val systate)
                               (all-addresses systate))))))
    :enable (committed-anchors
             validator-state->last-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             validator-state->dag-of-commit-anchors-next
             last-anchor-of-commit-anchors-next
             commit-anchors-possiblep
             collect-all-anchors
             certificate->round-of-cert-with-author+round
             pos-fix
             collect-anchors-of-extend-blockchain-no-change
             ordered-even-p-necc
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             evenp
             posp
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc
             active-committee-at-previous3-round-when-at-round))

  (defruled committed-anchors-of-commit-anchors-next-other-val
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val1 (correct-addresses systate))
                  (commit-anchors-possiblep val systate)
                  (addressp val)
                  (not (equal val1 val)))
             (equal (committed-anchors
                     (get-validator-state
                      val1 (commit-anchors-next val systate))
                     (all-addresses systate))
                    (committed-anchors
                     (get-validator-state val1 systate)
                     (all-addresses systate))))
    :enable (committed-anchors
             validator-state->last-of-commit-anchors-next
             validator-state->blockchain-of-commit-anchors-next
             validator-state->dag-of-commit-anchors-next
             last-anchor-of-commit-anchors-next))

  (defruled committed-anchors-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (accepted-certificate-committee-p systate)
                  (set::in val1 (correct-addresses systate))
                  (commit-anchors-possiblep val systate))
             (equal (committed-anchors
                     (get-validator-state
                      val1 (commit-anchors-next val systate))
                     (all-addresses systate))
                    (if (equal val1 (address-fix val))
                        (b* (((validator-state vstate)
                              (get-validator-state val1 systate))
                             (round (1- vstate.round))
                             (commtt (active-committee-at-round
                                      round
                                      vstate.blockchain
                                      (all-addresses systate)))
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
                                       vstate.blockchain
                                       (all-addresses systate))))
                          (append anchors
                                  (committed-anchors
                                   (get-validator-state val1 systate)
                                   (all-addresses systate))))
                      (committed-anchors
                       (get-validator-state val1 systate)
                       (all-addresses systate)))))
    :use (:instance lemma (val (address-fix val)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (ordered-even-p systate)
                     (last-blockchain-round-p systate)
                     (unequivocal-accepted-certificates-p systate)
                     (omni-paths-p systate)
                     (last-anchor-present-p systate)
                     (accepted-certificate-committee-p systate)
                     (set::in val1 (correct-addresses systate))
                     (commit-anchors-possiblep val systate)
                     (addressp val))
                (equal (committed-anchors
                        (get-validator-state
                         val1 (commit-anchors-next val systate))
                        (all-addresses systate))
                       (if (equal val1 (address-fix val))
                           (b* (((validator-state vstate)
                                 (get-validator-state val1 systate))
                                (round (1- vstate.round))
                                (commtt (active-committee-at-round
                                         round
                                         vstate.blockchain
                                         (all-addresses systate)))
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
                                          vstate.blockchain
                                          (all-addresses systate))))
                             (append anchors
                                     (committed-anchors
                                      (get-validator-state val1 systate)
                                      (all-addresses systate))))
                         (committed-anchors
                          (get-validator-state val1 systate)
                          (all-addresses systate)))))
       :use (committed-anchors-of-commit-anchors-next-last-not-0
             committed-anchors-of-commit-anchors-next-last-0
             committed-anchors-of-commit-anchors-next-other-val))))

  ;; timer-expires:

  (defruled committed-anchors-of-timer-expires-next
    (implies (and (set::in val (correct-addresses systate))
                  (timer-expires-possiblep val1 systate))
             (equal (committed-anchors
                     (get-validator-state
                      val (timer-expires-next val1 systate))
                     (all-addresses systate))
                    (committed-anchors
                     (get-validator-state val systate)
                     (all-addresses systate))))
    :enable (committed-anchors
             last-anchor-of-timer-expires-next
             validator-state->last-of-timer-expires-next
             validator-state->blockchain-of-timer-expires-next
             validator-state->dag-of-timer-expires-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-of-commit-anchors-next-to-collect-all-anchors
  :short "Rewriting of @(tsee committed-anchors) after @('commit-anchors')
          to @(tsee collect-all-anchors) on the old system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "While the theorem @('committed-anchors-of-commit-next')
     in @(see committed-anchors-of-next)
     expresses the new committed anchor sequence in terms of the old one,
     specifically as the @(tsee append) of the new anchors to the old ones,
     this theorem provides a different expression for
     the committed anchor sequence after a @('commit-anchors') event.
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
  (implies (and (ordered-even-p systate)
                (last-blockchain-round-p systate)
                (unequivocal-accepted-certificates-p systate)
                (omni-paths-p systate)
                (last-anchor-present-p systate)
                (accepted-certificate-committee-p systate)
                (commit-anchors-possiblep val systate))
           (equal (committed-anchors
                   (get-validator-state
                    val (commit-anchors-next val systate))
                   (all-addresses systate))
                  (b* (((validator-state vstate)
                        (get-validator-state val systate))
                       (round (1- vstate.round)))
                    (collect-all-anchors
                     (cert-with-author+round
                      (leader-at-round
                       round
                       (active-committee-at-round
                        round vstate.blockchain (all-addresses systate)))
                      round
                      vstate.dag)
                     vstate.dag
                     vstate.blockchain
                     (all-addresses systate)))))
  :use (:instance lemma (val (address-fix val)))
  :prep-lemmas
  ((defruled lemma
     (implies (and (ordered-even-p systate)
                   (last-blockchain-round-p systate)
                   (unequivocal-accepted-certificates-p systate)
                   (omni-paths-p systate)
                   (last-anchor-present-p systate)
                   (accepted-certificate-committee-p systate)
                   (addressp val)
                   (commit-anchors-possiblep val systate))
              (equal (committed-anchors
                      (get-validator-state
                       val (commit-anchors-next val systate))
                      (all-addresses systate))
                     (b* (((validator-state vstate)
                           (get-validator-state val systate))
                          (round (1- vstate.round)))
                       (collect-all-anchors
                        (cert-with-author+round
                         (leader-at-round
                          round
                          (active-committee-at-round
                           round vstate.blockchain (all-addresses systate)))
                         round
                         vstate.dag)
                        vstate.dag
                        vstate.blockchain
                        (all-addresses systate)))))
     :enable (commit-anchors-possiblep
              committed-anchors
              validator-state->last-of-commit-anchors-next
              validator-state->blockchain-of-commit-anchors-next
              validator-state->dag-of-commit-anchors-next
              last-anchor-of-commit-anchors-next
              collect-all-anchors-of-extend-blockchain-no-change
              ordered-even-p-necc
              blocks-ordered-even-p-of-extend-blockchain
              certificates-ordered-even-p-of-collect-anchors
              certificate->round-of-cert-with-author+round
              aleobft::evenp-of-1-less-when-not-evenp
              aleobft::evenp-of-3-less-when-not-evenp
              posp
              last-blockchain-round-p-necc
              collect-anchors-above-last-committed-round
              active-committee-at-previous-round-when-at-round))))
