; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STAKE2")

(include-book "nonforking-blockchains-next")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ simultaneous-induction
  :parents (correctness)
  :short "Proof by simultaneous induction for certain invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "As discussed in @(see unequivocal-dags-def-and-init)
     and in @(see nonforking-blockchains-def-and-init),
     these key invariants are proved by simultaneous induction.
     There are many other invariants involved,
     all of which are are proved to be preserved,
     through any sequence of events (via @(tsee events-next)),
     by simultaneous induction, in @(tsee invariants-of-events-next).
     This theorem is used, elsewhere, to prove theorems showing that
     individual invariants (among that set) hold in reachable states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled invariants-of-events-next
  :short "Preservation of a number of invariants
          by any sequence of zero or more events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by simultaneous induction,
     involving all of the invariants.")
   (xdoc::p
    "A critical assumption is fault tolerance:
     all the committees that arise during the execution
     must be fault-tolerant."))
  (implies (and (all-system-committees-fault-tolerant-p systate events)
                (backward-closed-p systate)
                (last-blockchain-round-p systate)
                (ordered-even-p systate)
                (signed-previous-quorum-p systate)
                (no-self-endorsed-p systate)
                (signer-records-p systate)
                (unequivocal-signed-certs-p systate)
                (signer-quorum-p systate)
                (unequivocal-dags-p systate)
                (nonforking-blockchains-p systate)
                (same-committees-p systate)
                (dag-previous-quorum-p systate)
                (last-anchor-present-p systate)
                (last-anchor-voters-p systate)
                (omni-paths-p systate)
                (nonforking-anchors-p systate)
                (committed-redundant-p systate)
                (blockchain-redundant-p systate)
                (events-possiblep events systate))
           (and (backward-closed-p (events-next events systate))
                (last-blockchain-round-p (events-next events systate))
                (ordered-even-p (events-next events systate))
                (signed-previous-quorum-p (events-next events systate))
                (no-self-endorsed-p (events-next events systate))
                (signer-records-p (events-next events systate))
                (unequivocal-signed-certs-p (events-next events systate))
                (signer-quorum-p (events-next events systate))
                (unequivocal-dags-p (events-next events systate))
                (nonforking-blockchains-p (events-next events systate))
                (same-committees-p (events-next events systate))
                (dag-previous-quorum-p (events-next events systate))
                (last-anchor-present-p (events-next events systate))
                (last-anchor-voters-p (events-next events systate))
                (omni-paths-p (events-next events systate))
                (nonforking-anchors-p (events-next events systate))
                (committed-redundant-p (events-next events systate))
                (blockchain-redundant-p (events-next events systate))))
  :induct t
  :enable (events-possiblep
           events-next
           all-system-committees-fault-tolerant-p))
