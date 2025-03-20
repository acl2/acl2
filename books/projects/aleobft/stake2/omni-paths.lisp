; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "simultaneous-induction")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ omni-paths
  :parents (correctness)
  :short "Invariant that the last committed anchor in a validator
          is also present and reachable from later certificates
          in any validator:
          proof that it holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This completes @(see omni-paths-def-and-implied)
     by showing that the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled omni-paths-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (and (system-state-reachablep systate)
                (system-committees-fault-tolerant-p systate))
           (omni-paths-p systate))
  :enable (system-state-reachablep
           backward-closed-p-when-init
           last-blockchain-round-p-when-init
           ordered-even-p-when-init
           signed-previous-quorum-p-when-init
           no-self-endorsed-p-when-init
           signer-records-p-when-init
           unequivocal-signed-certs-p-when-init
           signer-quorum-p-when-init
           unequivocal-dags-p-when-init
           nonforking-blockchains-p-when-init
           same-committees-p-implied
           dag-previous-quorum-p-when-init
           last-anchor-present-p-when-init
           last-anchor-voters-p-when-init
           omni-paths-p-implied
           nonforking-anchors-p-when-init
           committed-redundant-p-when-init
           blockchain-redundant-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (system-committees-fault-tolerant-p systate)
                   (backward-closed-p from)
                   (last-blockchain-round-p from)
                   (ordered-even-p from)
                   (signed-previous-quorum-p from)
                   (no-self-endorsed-p from)
                   (signer-records-p from)
                   (unequivocal-signed-certs-p from)
                   (signer-quorum-p from)
                   (unequivocal-dags-p from)
                   (nonforking-blockchains-p from)
                   (same-committees-p from)
                   (dag-previous-quorum-p from)
                   (last-anchor-present-p from)
                   (last-anchor-voters-p from)
                   (omni-paths-p from)
                   (nonforking-anchors-p from)
                   (committed-redundant-p from)
                   (blockchain-redundant-p from))
              (omni-paths-p systate))
     :enable (system-state-reachable-from-p
              all-system-committees-fault-tolerant-p-when-final)
     :use (:instance
           invariants-of-events-next
           (systate from)
           (events (system-state-reachable-from-p-witness systate from))))))
