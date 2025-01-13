; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE")

(include-book "dag-omni-paths")
(include-book "last-anchor-voters-def-and-init-and-next")
(include-book "backward-closure")
(include-book "previous-quorum-def-and-init-and-next")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ omni-paths-def-and-implied
  :parents (correctness)
  :short "Invariant that the last committed anchor in a validator
          is also present and reachable from later certificates
          in any validator:
          definition, and proof that it is implied by other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This lifts @(see dag-omni-paths) to the system level,
     and ties it with the invariant that
     the last committed anchor of each validator, if present,
     has more than @($f$) voting stake.")
   (xdoc::p
    "We define the invariant,
     and we prove that it is implied by other invariants.
     Elsewhere we prove that
     this invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk omni-paths-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          given two (equal or different) correct validators,
          if at least one anchor is committed in one,
          the other has a path to the same anchor
          from every certificate at least two rounds after the anchor."
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (b* ((vstate1 (get-validator-state val1 systate))
                        (vstate2 (get-validator-state val2 systate))
                        (anchor (last-anchor vstate1)))
                     (implies anchor
                              (dag-omni-paths-p
                               anchor
                               (validator-state->dag vstate2))))))
  ///
  (fty::deffixequiv-sk omni-paths-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omni-paths-p-implied
  :short "Proof of the invariant from other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key theorem that we use is @(tsee dag-omni-paths-p-holds).
     We use already proved invariant to establish its hypotheses."))
  (implies (and (backward-closed-p systate)
                (dag-committees-p systate)
                (unequivocal-dags-p systate)
                (same-committees-p systate)
                (previous-quorum-p systate)
                (last-anchor-voters-p systate))
           (omni-paths-p systate))
  :use ((:instance dag-omni-paths-p-holds
                   (dag1 (validator-state->dag
                          (get-validator-state
                           (mv-nth 0 (omni-paths-p-witness systate))
                           systate)))
                   (dag2 (validator-state->dag
                          (get-validator-state
                           (mv-nth 1 (omni-paths-p-witness systate))
                           systate)))
                   (blockchain1 (validator-state->blockchain
                                 (get-validator-state
                                  (mv-nth 0 (omni-paths-p-witness systate))
                                  systate)))
                   (blockchain2 (validator-state->blockchain
                                 (get-validator-state
                                  (mv-nth 1 (omni-paths-p-witness systate))
                                  systate)))
                   (cert (last-anchor (get-validator-state
                                       (mv-nth 0 (omni-paths-p-witness systate))
                                       systate))))
        (:instance last-anchor-voters-p-necc
                   (val (mv-nth 0 (omni-paths-p-witness systate)))))
  :enable (omni-paths-p
           unequivocal-dags-p-necc
           unequivocal-dags-p-necc-single
           backward-closed-p-necc
           dag-predecessor-quorum-p-when-previous-quorum-p
           validator-last-anchor-voters-p
           last-not-0-when-last-anchor
           certificate->round-of-last-anchor
           same-committees-p-necc
           dag-committees-p-necc
           last-anchor-in-dag))
