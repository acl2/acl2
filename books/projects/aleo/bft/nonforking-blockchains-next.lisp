; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

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
     (see @(see unequivocal-dags-def-and-init)
     and @(see unequivocal-dags-next)),
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
    "Elsewhere we prove that
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
    "The only event that may modify blockchains is @('commit').
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
     In @('lists-noforkp-of-blockchain-of-commit-next'),
     which provides most of the desired proof,
     we instantiate @('lists-noforkp-of-calculate-blockchain-when-anchors')
     with the committed anchors in the new state,
     and the DAGs in the new state, which are the same as in the old state
     (@('commit') does not change any DAGs).
     We need to use the redundancy of the blockchains invariant
     to rephrase the blockchains in terms of @(tsee calculate-blockchain),
     so that @('lists-noforkp-of-calculate-blockchain-when-anchors') applies.
     The main theorem @('nonforking-blockchains-p-of-commit-next')
     is then proved easily
     from @('lists-noforkp-of-blockchain-of-commit-next').")
   (xdoc::p
    "The other kinds of events do not modify the blockchain,
     and thus the preservation of non-forking is easy to prove."))

  ;; create:

  (defruled nonforking-blockchains-p-of-create-next
    (implies (and (nonforking-blockchains-p systate)
                  (create-possiblep cert systate))
             (nonforking-blockchains-p (create-next cert systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc))

  ;; accept:

  (defruled nonforking-blockchains-p-of-accept-next
    (implies (and (nonforking-blockchains-p systate)
                  (accept-possiblep msg systate))
             (nonforking-blockchains-p (accept-next msg systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc))

  ;; advance:

  (defruled nonforking-blockchains-p-of-advance-next
    (implies (and (nonforking-blockchains-p systate)
                  (advance-possiblep val systate))
             (nonforking-blockchains-p (advance-next val systate)))
    :enable (nonforking-blockchains-p
             nonforking-blockchains-p-necc))

  ;; commit:

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

  (defruled lists-noforkp-of-blockchain-of-commit-next
    (implies (and (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (signer-quorum-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (nonforking-anchors-p systate)
                  (committed-redundant-p systate)
                  (blockchain-redundant-p systate)
                  (commit-possiblep val systate)
                  (addressp val)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate)))
             (lists-noforkp
              (validator-state->blockchain
               (get-validator-state val1 (commit-next val systate)))
              (validator-state->blockchain
               (get-validator-state val2 (commit-next val systate)))))
    :enable (nonforking-anchors-p-of-commit-next
             blockchain-redundant-p-of-commit-next
             validator-blockchain-redundant-p
             unequivocal-dags-p-necc
             unequivocal-dags-p-necc-single
             backward-closed-p-necc
             last-anchor-present-p-of-commit-next)
    :use ((:instance nonforking-anchors-p-necc
                     (systate (commit-next val systate)))
          (:instance blockchain-redundant-p-necc
                     (val val1)
                     (systate (commit-next val systate)))
          (:instance blockchain-redundant-p-necc
                     (val val2)
                     (systate (commit-next val systate)))
          (:instance lists-noforkp-of-calculate-blockchain-when-anchors
                     (anchors1 (committed-anchors
                                (get-validator-state
                                 val1 (commit-next val systate))))
                     (anchors2 (committed-anchors
                                (get-validator-state
                                 val2 (commit-next val systate))))
                     (dag1 (validator-state->dag
                            (get-validator-state val1 systate)))
                     (dag2 (validator-state->dag
                            (get-validator-state val2 systate))))
          (:instance certificates-dag-paths-p-of-committed-anchors
                     (vstate (get-validator-state
                              val1 (commit-next val systate))))
          (:instance certificates-dag-paths-p-of-committed-anchors
                     (vstate (get-validator-state
                              val2 (commit-next val systate))))
          (:instance last-anchor-present-p-necc
                     (val val1)
                     (systate (commit-next val systate)))
          (:instance last-anchor-present-p-necc
                     (val val2)
                     (systate (commit-next val systate)))
          (:instance last-anchor-in-dag
                     (vstate (get-validator-state
                              val1 (commit-next val systate))))
          (:instance last-anchor-in-dag
                     (vstate (get-validator-state
                              val2 (commit-next val systate))))))

  (defruled nonforking-blockchains-p-of-commit-next
    (implies (and (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (signer-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (signer-quorum-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (nonforking-anchors-p systate)
                  (committed-redundant-p systate)
                  (blockchain-redundant-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (nonforking-blockchains-p (commit-next val systate)))
    :enable (nonforking-blockchains-p
             lists-noforkp-of-blockchain-of-commit-next))

  ;; all events:

  (defruled nonforking-blockchains-p-of-event-next
    (implies (and (nonforking-blockchains-p systate)
                  (backward-closed-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (unequivocal-dags-p systate)
                  (same-committees-p systate)
                  (signer-quorum-p systate)
                  (dag-previous-quorum-p systate)
                  (last-anchor-present-p systate)
                  (omni-paths-p systate)
                  (nonforking-anchors-p systate)
                  (committed-redundant-p systate)
                  (blockchain-redundant-p systate)
                  (event-possiblep event systate))
             (nonforking-blockchains-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))
