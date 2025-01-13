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
    "As discussed in @(see unequivocal-accepted-certificates-def-and-init)
     and in @(see nonforking-blockchains-def-and-init),
     these key invariants are proved by simultaneous induction.
     There are many other invariants involved,
     all of which are are proved to be preserved,
     through any sequence of events (via @(tsee events-next)),
     by simultaneous induction, in @(tsee invariants-of-events-next).
     This theorem can be used to prove theorems showing that
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
    "The hypothesis that the genesis committee
     consists of validators in the system
     serves to prove the @(tsee committees-in-system-p) invariant.")
   (xdoc::p
    "A critical assumption is fault tolerance:
     all the committees that arise during the execution
     must be fault-tolerant."))
  (implies
   (and (set::subset (committee-members (genesis-committee))
                     (all-addresses systate))
        (same-committees-p systate)
        (unequivocal-accepted-certificates-p systate)
        (last-anchor-voters-p systate)
        (omni-paths-p systate)
        (nonforking-anchors-p systate)
        (committed-redundant-p systate)
        (blockchain-redundant-p systate)
        (nonforking-blockchains-p systate)
        (same-owned-certificates-p systate)
        (no-self-messages-p systate)
        (no-self-buffer-p systate)
        (no-self-endorsed-p systate)
        (signer-records-p systate)
        (last-blockchain-round-p systate)
        (ordered-even-p systate)
        (accepted-certificate-committee-p systate)
        (signer-quorum-p systate)
        (previous-quorum-p systate)
        (backward-closed-p systate)
        (unequivocal-signed-certificates-p systate)
        (last-anchor-present-p systate)
        (committees-in-system-p systate)
        (rounds-in-committees-p systate)
        (events-possiblep events systate)
        (all-system-fault-tolerant-p events systate))
   (and (same-committees-p (events-next events systate))
        (unequivocal-accepted-certificates-p (events-next events systate))
        (last-anchor-voters-p (events-next events systate))
        (omni-paths-p (events-next events systate))
        (nonforking-anchors-p (events-next events systate))
        (committed-redundant-p (events-next events systate))
        (blockchain-redundant-p (events-next events systate))
        (nonforking-blockchains-p (events-next events systate))
        (same-owned-certificates-p (events-next events systate))
        (no-self-messages-p (events-next events systate))
        (no-self-buffer-p (events-next events systate))
        (no-self-endorsed-p (events-next events systate))
        (signer-records-p (events-next events systate))
        (last-blockchain-round-p (events-next events systate))
        (ordered-even-p (events-next events systate))
        (accepted-certificate-committee-p (events-next events systate))
        (signer-quorum-p (events-next events systate))
        (previous-quorum-p (events-next events systate))
        (backward-closed-p (events-next events systate))
        (unequivocal-signed-certificates-p (events-next events systate))
        (last-anchor-present-p (events-next events systate))
        (committees-in-system-p (events-next events systate))
        (rounds-in-committees-p (events-next events systate))))
  :induct t
  :enable (events-possiblep
           events-next
           all-system-fault-tolerant-p
           committees-in-system-p-when-genesis
           rounds-in-committees-p-invariant
           same-committees-p-implied
           unequivocal-accepted-certificates-p-of-event-next
           last-anchor-voters-p-of-event-next
           omni-paths-p-implied
           nonforking-anchors-p-of-event-next
           committed-redundant-p-of-event-next
           blockchain-redundant-p-of-event-next
           nonforking-blockchains-p-of-event-next
           same-owned-certificates-p-of-event-next
           no-self-messages-p-of-event-next
           no-self-buffer-p-of-event-next
           no-self-endorsed-p-of-event-next
           signer-records-p-of-event-next
           last-blockchain-round-p-of-event-next
           ordered-even-p-of-event-next
           accepted-certificate-committee-p-of-event-next
           signer-quorum-p-of-event-next
           previous-quorum-p-of-event-next
           backward-closed-p-of-event-next
           unequivocal-signed-certificates-p-of-event-next
           last-anchor-present-p-of-event-next))
