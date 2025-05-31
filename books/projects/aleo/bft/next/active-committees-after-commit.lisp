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

(include-book "last-blockchain-round")
(include-book "ordered-blockchain")

(local (include-book "../library-extensions/arithmetic-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ active-committees-after-commit
  :parents (correctness)
  :short "Invariance of active committees under @('commit') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each validator calculates active committees
     (for the rounds for which it can)
     based on its own copy of the blockchain.
     The only event that modifies blockchains is @('commit'),
     but it does so in a way that does not affect
     the calculation of active committees
     that it could already calculate:
     the blockchain is modified by being extended;
     after the extension, the validator may calculate
     active committees for additional rounds,
     but the calculation for previous rounds is not affected.")
   (xdoc::p
    "Here we prove a theorem about this,
     which is used in several other proofs.
     This theorem needs two already proved invariants."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled active-committee-at-round-of-commit-next
  :short "Invariance of @(tsee active-committee-at-round)
          under @(tsee commit-next)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The key theorem is
     @('active-committee-at-round-of-extend-blockchain-no-change'),
     but we need other rules to relieve the hypotheses."))
  (implies (and (commit-possiblep val systate)
                (last-blockchain-round-p systate)
                (ordered-blockchain-p systate)
                (active-committee-at-round
                 round
                 (validator-state->blockchain
                  (get-validator-state val1 systate))))
           (equal (active-committee-at-round
                   round
                   (validator-state->blockchain
                    (get-validator-state val1 (commit-next val systate))))
                  (active-committee-at-round
                   round
                   (validator-state->blockchain
                    (get-validator-state val1 systate)))))
  :enable (validator-state->blockchain-of-commit-next
           active-committee-at-round-of-extend-blockchain-no-change
           blocks-orderedp-of-extend-blockchain
           cert-list-orderedp-of-collect-anchors
           cert-list-evenp-of-collect-anchors
           commit-possiblep
           aleobft::evenp-of-1-less-when-not-evenp
           aleobft::evenp-of-3-less-when-not-evenp
           ordered-blockchain-p-necc-with-address-fix
           last-blockchain-round-p-necc-with-address-fix
           collect-anchors-above-last-committed-round
           nfix))
