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

(include-book "committed-anchor-sequences")

(local (include-book "library-extensions/arithmetic-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ nonforking-anchors-def-and-init-and-next
  :parents (correctness)
  :short "Invariant that committed anchors do not fork:
          definition, establishment, and preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is most of what is needed to show the non-forking of blockchains,
     given that, as proved elsewhere, the blockchain in each validator
     is determined by the anchors committed so far.")
   (xdoc::p
    "The non-forking of anchors could be proved from existing invariants,
     but if we did that, the final proof by induction would not work.
     Recall that we need to prove non-equivocation and blockchain non-forking
     simultaneously by induction, as discussed in
     @(see unequivocal-dags-def-and-init) and
     @(see nonforking-blockchains-def-and-init).
     If we just proved the non-forking of anchors
     from existing invariants, which include non-equivocation,
     which depends on blockchain non-forking,
     and then proved non-forking of blockchains from non-forking of anchors,
     things would be circular, and not in the way that works with induction.
     Thus, here we prove the non-forking of anchors by showing that
     it is established in the initial states and
     it is preserved by all transitions.")
   (xdoc::p
    "Initially no anchors are committed, so clearly there is no forking.
     The only kind of events that changes the committed anchors
     is @('commit'), which extends them.
     There are a few cases to consider,
     but in all cases the extension cannot cause forking;
     this is explained in detail below,
     in the proofs of preservation.")
   (xdoc::p
    "Here we define the invariant,
     we prove that it holds in all initial states,
     and we prove that it is preserved by all transitions.
     Elsewhere we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk nonforking-anchors-p ((systate system-statep))
  :guard (and (last-blockchain-round-p systate)
              (ordered-blockchain-p systate)
              (last-anchor-present-p systate))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          given two correct validators in the system,
          their sequences of committed anchor do not fork."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (lists-noforkp
                    (committed-anchors (get-validator-state val1 systate))
                    (committed-anchors (get-validator-state val2 systate)))))
  :guard-hints (("Goal" :in-theory (enable evenp-of-last-when-ordered-blockchain-p
                                           last-anchor-present-p-necc)))
  ///
  (fty::deffixequiv-sk nonforking-anchors-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled nonforking-anchors-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially the committed anchors are the same (both empty),
     so they clearly do not fork.
     The proof does not even depend on their emptiness,
     just their equality, since both validators' states
     is @(tsee validator-init)."))
  (implies (system-initp systate)
           (nonforking-anchors-p systate))
  :enable (nonforking-anchors-p
           system-initp
           system-validators-initp-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonforking-anchors-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that may modify the committed anchors
     is @('commit'), whose preservation proof is explained below.
     For the other five kinds of events, the proof of preservation is easy,
     because @(tsee committed-anchors) does not change
     as proved in @(see committed-anchors-of-next),
     and so if there was no fork before there is no fork after either.")
   (xdoc::p
    "To prove the preservation of anchor non-forking under @('commit'),
     we need to show that, in the new state,
     the committed anchor sequences of any two validators do not fork.
     There are a few cases to consider.")
   (xdoc::p
    "If neither of those two validator is the one that commits anchors,
     their committed anchor sequences do not change,
     and thus if they were not forking before, they are still not forking.
     This case is covered by the local lemma @('case-others'),
     whose proof is easy by using @('committed-anchors-of-commit-next')
     to rewrite @(tsee committed-anchors) to the previous values.
     Otherwise, at least one of the validators must be @('val'),
     i.e. the one that commits anchors.
     If both validators are @('val'), then the non-forking is trivial:
     this case does not even need a lemma;
     it gets taken care of in the proof of
     @('nonforking-anchors-p-of-commit-next-lemma'),
     which is the main lemma that proves the final theorem.
     So below we consider the possible cases of
     one validator being @('val')
     and the other being a different one @('val0').")
   (xdoc::p
    "There are three cases to consider,
     based on whether the last committed round of @('val0')
     is equal to, or less than, or greater than
     the newly committed round of @('val'),
     which is one less than the current round of @('val').
     That is, the three cases are whether last committed round of @('val0') is
     aligned with, behind, or ahead of the newly committed round of @('val'):
     these three cases are covered by the three local lemmas
     @('case-other-aligned'), @('case-other-behind'), and @('case-other-ahead'),
     which we now explain.")
   (xdoc::p
    "Common to the three cases and lemmas
     is the handling of the @(tsee committed-anchors) calls.
     The one on @('val0') is reduced to the old value,
     via the @('committed-anchors-of-commit-next') rule,
     and then the @(':expand') hint turns that into
     a call of @(tsee collect-all-anchors).
     But the one on @('val') is rewritten
     not via @('committed-anchors-of-commit-next'),
     which would result in an @(tsee append),
     but via @('committed-anchors-of-commit-next-to-collect-all-anchors'),
     which produces directly a call of @(tsee collect-all-anchors).
     For this to work, it is critical that
     @('committed-anchors-of-commit-next-to-collect-all-anchors')
     is introduced after @('committed-anchors-of-commit-next'),
     and thus it is reliably tried first by ACL2,
     according to its ordered history of events.
     The reason why we use an @(':expand') hint,
     instead of just enabling @(tsee committed-anchors),
     is that it would interfere with the two rewrite rules.
     Any case, this strategy results in @(tsee lists-noforkp)
     applied to two calls of @(tsee collect-all-anchors),
     in all three lemmas.")
   (xdoc::p
    "Another commonality among the three lemmas is that
     they do not need the hypothesis that
     @(tsee nonforking-anchors-p) holds on the old state.
     That hypothesis is not needed, because we prove the non-forking
     directly on the two calls of @(tsee collect-all-anchors)
     that result from the proof strategy described above.
     Note that, when the committed anchors of @('val') are extended,
     they may become aligned with, or behind, or ahead of,
     the committed anchors of @('val0'),
     regardless of whether, in the old state,
     they were aligned, or behind, or ahead;
     it is indeed simpler to just consider the two new anchor sequences,
     without regard to the two old anchor sequences.")
   (xdoc::p
    "In the lemma @('case-other-aligned'),
     the last anchor committed by @('val0') (which does not change),
     and the new anchor committed by @('val'),
     are the same certificate,
     because they are at the same round (by hypothesis of the case),
     and because the leader at that common round is also the same,
     given that committees agree across @('val') and @('val0').
     The fact that the two certificate are equal
     is proved via @('cert-with-author+round-of-unequivocal-sets'),
     and then the key theorem is @('collect-all-anchors-of-unequivocal-dags'),
     which says that the anchors collected from a common certificate
     are the same in the two validators.
     The rest of the hints in the proof serve to
     relieve hypotheses of these two key theorems we use.")
   (xdoc::p
    "In the lemma @('case-other-behind'),
     the last anchor committed by @('val0') (which does not change)
     is behind the new anchor committed by @('val').
     We already proved in @(tsee omni-paths-p-implied)
     that, since the last anchor of @('val0') has at least @($f+1$) votes,
     there are paths to it in every DAG (including the one of @('val')),
     from certificates at least two rounds ahead.
     By hypothesis of the case, the new anchor committed by @('val')
     is ahead of the last anchor of @('val0'),
     and they are all at even rounds,
     so it is at least two rounds ahead.
     So the key theorem we apply here is
     @('collect-all-anchors-to-append-of-collect-anchors-dags'),
     which lets us rewrite the new anchors committed by @('val'),
     expressed as a call of @(tsee collect-all-anchors) as explained above,
     as an append of something (irrelevant here) to
     the anchors committed by @('val0'),
     from which @(tsee lists-noforkp) follows
     (via enabled rules about that function).
     The rest of the hints in @('case-other-behind')
     serve to relieve the hypotheses of the key theorem we use in the proof.")
   (xdoc::p
    "In the lemma @('case-other-ahead'),
     the last anchor committed by @('val0') (which does not change)
     is ahead of the new anchor committed by @('val').
     The key theorem in this proof is again
     @('collect-all-anchors-to-append-of-collect-anchors-dags'),
     with the roles of the validators swapped.
     But here we can no longer obtain
     the omni-paths property directly from an invariant as in the previous case.
     But the property still holds,
     given that the new committed anchor of @('val')
     has more than @($f$) voting stake.
     So we prove, just before the lemma for the case,
     the theorem @('dag-omni-paths-p-when-commit-possiblep'),
     which says that the omni-paths property holds
     when @(tsee commit-possiblep) holds.
     The key theorem in that proof is @('dag-omni-paths-p-holds'),
     whose hypotheses are all fairly direct to relieve,
     but note that we need to use
     @('stake-of-successors-to-leader-stake-votes')
     as a bridge between the greater than @($f$) hypothesis
     of @('dag-omni-paths-p-holds'),
     which is in terms of @(tsee successors),
     and the greater than @($f$) check performed by @(tsee commit-possiblep),
     which is in terms of @(tsee leader-stake-votes).
     Back to the lemma @('case-other-ahead'),
     we use the just proved @('dag-omni-paths-p-when-commit-possiblep')
     to relieve the hypothesis about omni-paths of
     @('collect-all-anchors-to-append-of-collect-anchors-dags').
     So the proof of this @('case-other-ahead')
     is fairly similar to @('case-other-behind'),
     except for how we discharge the omni-paths hypothesis.")
   (xdoc::p
    "The local lemma @('nonforking-anchors-p-of-commit-next-lemma')
     uses the four @('case-...') lemmas described above.
     Since the lemma is over generic @('val1') and @('val2'),
     we need to instantiate each the three latter lemmas twice,
     with @('val0') playing the role of @('val1') or @('val2').
     The lemma @('case-others') is only used once,
     because it is already formulated on @('val1') and @('val2').
     Attempting to use these four lemmas just as rewrite rules
     does not make the proof succeed:
     they would probably necessitate a @(':cases') hint
     corresponding to the cases of the lemmas,
     but the @(':use') hint looks simpler and shorter.")
   (xdoc::p
    "From @('nonforking-anchors-p-of-commit-next-lemma'),
     the main theorem @('nonforking-anchors-p-of-commit-next')
     easily follows."))

  ;; create:

  (defruled nonforking-anchors-p-of-create-next
    (implies (and (nonforking-anchors-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (create-possiblep cert systate))
             (nonforking-anchors-p (create-next cert systate)))
    :enable (nonforking-anchors-p
             nonforking-anchors-p-necc))

  ;; accept:

  (defruled nonforking-anchors-p-of-accept-next
    (implies (and (nonforking-anchors-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-signed-certs-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (accept-possiblep msg systate)
                  (messagep msg))
             (nonforking-anchors-p (accept-next msg systate)))
    :enable (nonforking-anchors-p
             nonforking-anchors-p-necc))

  ;; advance:

  (defruled nonforking-anchors-p-of-advance-next
    (implies (and (nonforking-anchors-p systate)
                  (advance-possiblep val systate))
             (nonforking-anchors-p (advance-next val systate)))
    :enable (nonforking-anchors-p
             nonforking-anchors-p-necc))

  ;; commit:

  (defruledl case-others
    (implies (and (nonforking-anchors-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate))
                  (not (equal val1 val))
                  (not (equal val2 val)))
             (lists-noforkp
              (committed-anchors (get-validator-state
                                  val1 (commit-next val systate)))
              (committed-anchors (get-validator-state
                                  val2 (commit-next val systate)))))
    :enable (nonforking-anchors-p-necc
             committed-anchors-of-commit-next))

  (defruledl case-other-aligned
    (implies (and (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val0 (correct-addresses systate))
                  (not (equal val0 val))
                  (equal (validator-state->last
                          (get-validator-state val0 systate))
                         (1- (validator-state->round
                              (get-validator-state val systate)))))
             (lists-noforkp
              (committed-anchors
               (get-validator-state val0 (commit-next val systate)))
              (committed-anchors
               (get-validator-state val (commit-next val systate)))))
    :enable (committed-anchors-of-commit-next-to-collect-all-anchors
             committed-anchors-of-commit-next
             commit-possiblep
             last-anchor
             same-committees-p-necc
             active-committee-at-previous-round-when-at-round
             unequivocal-dags-p-necc
             unequivocal-dags-p-necc-single
             backward-closed-p-necc
             dag-has-committees-p-when-signer-quorum-p
             dag-in-committees-p-when-signer-quorum-p
             cert-with-author+round-element)
    :expand (committed-anchors (get-validator-state val0 systate))
    :use ((:instance last-anchor-present-p-necc (val val0))
          (:instance same-active-committees-p-necc
                     (blocks1 (validator-state->blockchain
                               (get-validator-state val systate)))
                     (blocks2 (validator-state->blockchain
                               (get-validator-state val0 systate)))
                     (round (validator-state->last
                             (get-validator-state val0 systate))))
          (:instance cert-with-author+round-of-unequivocal-sets
                     (author
                      (leader-at-round
                       (validator-state->last
                        (get-validator-state val0 systate))
                       (active-committee-at-round
                        (validator-state->last
                         (get-validator-state val0 systate))
                        (validator-state->blockchain
                         (get-validator-state val systate)))))
                     (round
                      (validator-state->last
                       (get-validator-state val0 systate)))
                     (certs1 (validator-state->dag
                              (get-validator-state val systate)))
                     (certs2 (validator-state->dag
                              (get-validator-state val0 systate))))
          (:instance collect-all-anchors-of-unequivocal-dags
                     (dag1 (validator-state->dag
                            (get-validator-state val systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state val0 systate)))
                     (blockchain1 (validator-state->blockchain
                                   (get-validator-state val systate)))
                     (blockchain2 (validator-state->blockchain
                                   (get-validator-state val0 systate)))
                     (last-anchor (last-anchor
                                   (get-validator-state val0 systate))))))

  (defruledl case-other-behind
    (implies (and (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val0 (correct-addresses systate))
                  (not (equal val0 val))
                  (< (validator-state->last
                      (get-validator-state val0 systate))
                     (1- (validator-state->round
                          (get-validator-state val systate)))))
             (lists-noforkp
              (committed-anchors
               (get-validator-state val0 (commit-next val systate)))
              (committed-anchors
               (get-validator-state val (commit-next val systate)))))
    :enable (committed-anchors-of-commit-next-to-collect-all-anchors
             committed-anchors-of-commit-next
             commit-possiblep
             unequivocal-dags-p-necc
             unequivocal-dags-p-necc-single
             dag-has-committees-p-when-signer-quorum-p
             dag-in-committees-p-when-signer-quorum-p
             backward-closed-p-necc
             cert-with-author+round-element
             omni-paths-p-necc
             last-anchor-present-p-necc
             evenp-of-1-less-when-not-evenp
             last-anchor-in-dag
             same-committees-p-necc
             certificate->author-of-last-anchor
             certificate->round-of-last-anchor
             last-blockchain-round-p-necc
             ordered-blockchain-p-necc)
    :expand (committed-anchors (get-validator-state val0 systate))
    :use (:instance collect-all-anchors-to-append-of-collect-anchors-dags
                    (dag1 (validator-state->dag
                           (get-validator-state val0 systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state val systate)))
                    (blockchain1 (validator-state->blockchain
                                  (get-validator-state val0 systate)))
                    (blockchain2 (validator-state->blockchain
                                  (get-validator-state val systate)))
                    (anchor1 (last-anchor (get-validator-state val0 systate)))
                    (anchor2 (cert-with-author+round
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
                               (get-validator-state val systate))))))

  (defruled dag-omni-paths-p-when-commit-possiblep
    (implies (and (backward-closed-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (dag-previous-quorum-p systate)
                  (set::in val0 (correct-addresses systate))
                  (commit-possiblep val systate)
                  (addressp val))
             (dag-omni-paths-p (cert-with-author+round
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
                                 (get-validator-state val systate)))
                               (validator-state->dag
                                (get-validator-state val0 systate))))
    :enable (commit-possiblep
             unequivocal-dags-p-necc
             unequivocal-dags-p-necc-single
             dag-has-committees-p-when-signer-quorum-p
             dag-in-committees-p-when-signer-quorum-p
             dag-predecessor-quorum-p-when-dag-previous-quorum-p
             cert-with-author+round-element
             backward-closed-p-necc
             fix
             stake-of-successors-to-leader-stake-votes
             same-committees-p-necc)
    :use (:instance dag-omni-paths-p-holds
                    (dag1 (validator-state->dag
                           (get-validator-state val systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state val0 systate)))
                    (blockchain1 (validator-state->blockchain
                                  (get-validator-state val systate)))
                    (blockchain2 (validator-state->blockchain
                                  (get-validator-state val0 systate)))
                    (cert (cert-with-author+round
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
                            (get-validator-state val systate))))))

  (defruledl case-other-ahead
    (implies (and (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val0 (correct-addresses systate))
                  (not (equal val0 val))
                  (> (validator-state->last
                      (get-validator-state val0 systate))
                     (1- (validator-state->round
                          (get-validator-state val systate)))))
             (lists-noforkp
              (committed-anchors
               (get-validator-state val0 (commit-next val systate)))
              (committed-anchors
               (get-validator-state val (commit-next val systate)))))
    :enable (committed-anchors-of-commit-next-to-collect-all-anchors
             committed-anchors-of-commit-next
             commit-possiblep
             unequivocal-dags-p-necc
             unequivocal-dags-p-necc-single
             dag-has-committees-p-when-signer-quorum-p
             dag-in-committees-p-when-signer-quorum-p
             backward-closed-p-necc
             last-anchor-present-p-necc
             last-anchor-in-dag
             evenp-of-1-less-when-not-evenp
             same-committees-p-necc
             dag-omni-paths-p-when-commit-possiblep
             certificate->round-of-last-anchor
             last-blockchain-round-p-necc
             ordered-blockchain-p-necc
             cert-with-author+round-element)
    :expand (committed-anchors (get-validator-state val0 systate))
    :use (:instance collect-all-anchors-to-append-of-collect-anchors-dags
                    (dag1 (validator-state->dag
                           (get-validator-state val systate)))
                    (dag2 (validator-state->dag
                           (get-validator-state val0 systate)))
                    (blockchain1 (validator-state->blockchain
                                  (get-validator-state val systate)))
                    (blockchain2 (validator-state->blockchain
                                  (get-validator-state val0 systate)))
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
                    (anchor2 (last-anchor (get-validator-state val0 systate)))))

  (defruled nonforking-anchors-p-of-commit-next-lemma
    (implies (and (nonforking-anchors-p systate)
                  (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate)))
             (lists-noforkp
              (committed-anchors
               (get-validator-state val1 (commit-next val systate)))
              (committed-anchors
               (get-validator-state val2 (commit-next val systate)))))
    :use (case-others
          (:instance case-other-aligned (val0 val1))
          (:instance case-other-aligned (val0 val2))
          (:instance case-other-behind (val0 val1))
          (:instance case-other-behind (val0 val2))
          (:instance case-other-ahead (val0 val1))
          (:instance case-other-ahead (val0 val2))))

  (defruled nonforking-anchors-p-of-commit-next
    (implies (and (nonforking-anchors-p systate)
                  (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (nonforking-anchors-p (commit-next val systate)))
    :expand (nonforking-anchors-p (commit-next val systate))
    :enable nonforking-anchors-p-of-commit-next-lemma)

  ;; all events:

  (defruled nonforking-anchors-p-of-event-next
    (implies (and (nonforking-anchors-p systate)
                  (system-committees-fault-tolerant-p systate)
                  (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-blockchain-p systate)
                  (no-self-endorsed-p systate)
                  (signer-records-p systate)
                  (unequivocal-signed-certs-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (event-possiblep event systate))
             (nonforking-anchors-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
