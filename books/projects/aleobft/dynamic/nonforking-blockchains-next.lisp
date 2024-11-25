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

(include-book "nonforking-anchors-def-and-init-and-next")
(include-book "blockchain-redundant-def-and-init-and-next")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ nonforking-blockchains-next
  :parents (correctness)
  :short "Invariant that blockchains do not fork:
          preservation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(see nonforking-blockchains-def-and-init),
     the preservation of blockchain non-forking is proved
     separately from its definition and establishment proof,
     as done for certificate non-equivocation
     (see @(see unequivocal-accepted-certificates-def-and-init)
     and @(see unequivocal-accepted-certificates-next)),
     due to the need for simultaneous induction.
     Although it would be possible to prove the non-forking of blockchains
     from other invariants, particularly the non-forking of anchors,
     some of these invariants depend on blockchain non-forking,
     so this would not work for a proof by induction.
     Instead, as also done for anchors non-forking
     (see @(see nonforking-anchors)),
     we need to prove the preservation of blockchain non-forking
     from old state to new state.")
   (xdoc::p
    "In @(see nonforking-blockchains) we prove that
     the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection nonforking-blockchains-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only event that may modify blockchains is @('commit-anchors').
     To prove that blockchains in the new state do not fork,
     we do not need to assume that in the old state:
     it suffices to assume the non-forking of anchors in the old state,
     along with a number of other invariants,
     and then we use the already proved
     preservation of that and other invariants
     to show the non-forking of blockchains in the new state.
     First we prove a theorem,
     @('lists-noforkp-of-calculate-blockchain-when-anchors'),
     that lifts the non-forking of two anchor sequences
     to the non-forking of two blockchains
     calculated from the anchors from two DAGs.
     In @('lists-noforkp-of-blockchain-of-commit-anchors-next'),
     which provides most of the desired proof,
     we instantiate @('lists-noforkp-of-calculate-blockchain-when-anchors')
     with the committed anchors in the new state,
     and the DAGs in the new state, which are the same as in the old state
     (@('commit-anchors') does not change any DAGs).
     We disable tau to make the proof more explicit
     in its use of some of the already proved invariant preservation theorems.
     We need to use the redundancy of the blockchains invariant
     to rephrase the blockchains in terms of @(tsee calculate-blockchain),
     so that @('lists-noforkp-of-calculate-blockchain-when-anchors') applies.
     The main theorem @('nonforking-blockchains-p-of-commit-anchors-next')
     is then proved easily
     from @('lists-noforkp-of-blockchain-of-commit-anchors-next').")
   (xdoc::p
    "The other five kinds of events do not modify the blockchain,
     and thus the preservation of non-forking is easy to prove."))

  ;; create-certificate:

  (defruled nonforking-blockchains-p-of-create-certificate-next
    (implies (and (nonforking-blockchains-p systate)
                  (create-certificate-possiblep cert systate))
             (nonforking-blockchains-p
              (create-certificate-next cert systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc
             validator-state->blockchain-of-create-certificate-next))

  ;; receive-certificate:

  (defruled nonforking-blockchains-p-of-receive-certificate-next
    (implies (and (nonforking-blockchains-p systate)
                  (receive-certificate-possiblep msg systate))
             (nonforking-blockchains-p
              (receive-certificate-next msg systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc
             validator-state->blockchain-of-receive-certificate-next))

  ;; store-certificate:

  (defruled nonforking-blockchains-p-of-store-certificate-next
    (implies (and (nonforking-blockchains-p systate)
                  (store-certificate-possiblep val cert systate))
             (nonforking-blockchains-p
              (store-certificate-next val cert systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc
             validator-state->blockchain-of-store-certificate-next))

  ;; advance-round:

  (defruled nonforking-blockchains-p-of-advance-round-next
    (implies (and (nonforking-blockchains-p systate)
                  (advance-round-possiblep val systate))
             (nonforking-blockchains-p
              (advance-round-next val systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc
             validator-state->blockchain-of-advance-round-next))

  ;; commit-anchors:

  (defruled lists-noforkp-of-calculate-blockchain-when-anchors
    (implies (and (lists-noforkp anchors1 anchors2)
                  (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (certificates-dag-paths-p anchors1 dag1)
                  (certificates-dag-paths-p anchors2 dag2))
             (lists-noforkp (calculate-blockchain anchors1 dag1)
                            (calculate-blockchain anchors2 dag2)))
    :enable (lists-noforkp
             len-of-calculate-blockchain
             nthcdr-of-calculate-blockchain
             list-in-when-certificates-dag-paths-p)
    :use ((:instance calculate-blockchain-of-unequivocal-dags
                     (anchors anchors1))
          (:instance calculate-blockchain-of-unequivocal-dags
                     (anchors anchors2))))

  (defruled lists-noforkp-of-blockchain-of-commit-anchors-next
    (implies (and (nonforking-anchors-p systate)
                  (blockchain-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (backward-closed-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (same-committees-p systate)
                  (signer-quorum-p systate)
                  (previous-quorum-p systate)
                  (committed-redundant-p systate)
                  (commit-anchors-possiblep val systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate)))
             (lists-noforkp
              (validator-state->blockchain
               (get-validator-state
                val1 (commit-anchors-next val systate)))
              (validator-state->blockchain
               (get-validator-state
                val2 (commit-anchors-next val systate)))))
    :disable ((:e tau-system))
    :enable (nonforking-anchors-p-of-commit-anchors-next
             blockchain-redundant-p-of-commit-anchors-next
             validator-blockchain-redundant-p
             validator-state->dag-of-commit-anchors-next
             certificate-set-unequivocalp-when-unequivocal-accepted
             certificate-sets-unequivocalp-when-unequivocal-accepted
             backward-closed-p-necc
             last-anchor-present-p-of-commit-anchors-next)
    :use ((:instance nonforking-anchors-p-necc
                     (systate (commit-anchors-next val systate)))
          (:instance blockchain-redundant-p-necc
                     (val val1)
                     (systate (commit-anchors-next val systate)))
          (:instance blockchain-redundant-p-necc
                     (val val2)
                     (systate (commit-anchors-next val systate)))
          (:instance lists-noforkp-of-calculate-blockchain-when-anchors
                     (anchors1 (committed-anchors
                                (get-validator-state
                                 val1 (commit-anchors-next val systate))
                                (all-addresses systate)))
                     (anchors2 (committed-anchors
                                (get-validator-state
                                 val2 (commit-anchors-next val systate))
                                (all-addresses systate)))
                     (dag1 (validator-state->dag
                            (get-validator-state val1 systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state val2 systate))))
          (:instance certificates-dag-paths-p-of-committed-anchors
                     (vstate (get-validator-state
                              val1 (commit-anchors-next val systate)))
                     (all-vals (all-addresses systate)))
          (:instance certificates-dag-paths-p-of-committed-anchors
                     (vstate (get-validator-state
                              val2 (commit-anchors-next val systate)))
                     (all-vals (all-addresses systate)))
          (:instance last-anchor-present-p-necc
                     (val val1)
                     (systate (commit-anchors-next val systate)))
          (:instance last-anchor-present-p-necc
                     (val val2)
                     (systate (commit-anchors-next val systate)))
          (:instance last-anchor-in-dag
                     (vstate (get-validator-state
                              val1 (commit-anchors-next val systate)))
                     (all-vals (all-addresses systate)))
          (:instance last-anchor-in-dag
                     (vstate (get-validator-state
                              val2 (commit-anchors-next val systate)))
                     (all-vals (all-addresses systate)))))

  (defruled nonforking-blockchains-p-of-commit-anchors-next
    (implies (and (nonforking-anchors-p systate)
                  (blockchain-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (backward-closed-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (same-committees-p systate)
                  (signer-quorum-p systate)
                  (previous-quorum-p systate)
                  (committed-redundant-p systate)
                  (commit-anchors-possiblep val systate))
             (nonforking-blockchains-p
              (commit-anchors-next val systate)))
    :enable (nonforking-blockchains-p
             lists-noforkp-of-blockchain-of-commit-anchors-next))

  ;; timer-expires:

  (defruled nonforking-blockchains-p-of-timer-expires-next
    (implies (and (nonforking-blockchains-p systate)
                  (timer-expires-possiblep val systate))
             (nonforking-blockchains-p
              (timer-expires-next val systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc
             validator-state->blockchain-of-timer-expires-next))

  ;; all events:

  (defruled nonforking-blockchains-p-of-event-next
    (implies (and (nonforking-blockchains-p systate)
                  (nonforking-anchors-p systate)
                  (blockchain-redundant-p systate)
                  (unequivocal-accepted-certificates-p systate)
                  (backward-closed-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (accepted-certificate-committee-p systate)
                  (omni-paths-p systate)
                  (last-anchor-present-p systate)
                  (same-committees-p systate)
                  (signer-quorum-p systate)
                  (previous-quorum-p systate)
                  (committed-redundant-p systate)
                  (event-possiblep event systate))
             (nonforking-blockchains-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
