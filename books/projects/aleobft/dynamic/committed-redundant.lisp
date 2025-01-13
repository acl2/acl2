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

(include-book "simultaneous-induction")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committed-redundant
  :parents (correctness)
  :short "Invariant that the set of committed certificates is redundant:
          proof that it holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "This completes @(see committed-redundant-def-and-init-and-next)
     by showing that the invariant holds in every reachable state."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection committed-redundant-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled committed-redundant-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate)
                  (all-system-fault-tolerant-p events systate))
             (committed-redundant-p (events-next events systate)))
    :enable (same-committees-p-implied
             unequivocal-accepted-certificates-p-when-init
             last-anchor-voters-p-when-init
             omni-paths-p-implied
             nonforking-anchors-p-when-init
             committed-redundant-p-when-init
             blockchain-redundant-p-when-init
             nonforking-blockchains-p-when-init
             same-owned-certificates-p-when-init
             no-self-messages-p-when-init
             no-self-buffer-p-when-init
             no-self-endorsed-p-when-init
             signer-records-p-when-init
             last-blockchain-round-p-when-init
             ordered-even-p-when-init
             accepted-certificate-committee-p-when-init
             signer-quorum-p-when-init
             previous-quorum-p-when-init
             backward-closed-p-when-init
             unequivocal-signed-certificates-p-when-init
             last-anchor-present-p-when-init
             committees-in-system-p-when-genesis
             rounds-in-committees-p-invariant
             system-initp
             invariants-of-events-next)))
