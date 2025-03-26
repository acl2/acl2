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

(include-book "last-blockchain-round")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ordered-even-blocks
  :parents (correctness)
  :short "Invariant that blocks in validators' blockchains
          have strictly increasing, even round numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "Blocks are committed to even rounds,
     so all the block round numbers are even.
     Furthermore, blocks are committed as rounds increase,
     so blocks have strictly increasing round numbers in the blockchain."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk ordered-even-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the blockchain of every correct validator has
          strictly increasing, even round numbers."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (blocks-ordered-even-p
                    (validator-state->blockchain
                     (get-validator-state val systate)))))

  ///

  (fty::deffixequiv-sk ordered-even-p
    :args ((systate system-statep)))

  (defruled ordered-even-p-necc-fixing
    (implies (and (ordered-even-p systate)
                  (set::in (address-fix val) (correct-addresses systate)))
             (blocks-ordered-even-p
              (validator-state->blockchain
               (get-validator-state val systate))))
    :use (:instance ordered-even-p-necc (val (address-fix val))))

  (defruled evenp-of-last-when-ordered-even-p
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (set::in val (correct-addresses systate)))
             (evenp (validator-state->last
                     (get-validator-state val systate))))
    :enable (evenp-of-blocks-last-round
             last-blockchain-round-p-necc)
    :disable ordered-even-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled ordered-even-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  (implies (system-initp systate)
           (ordered-even-p systate))
  :enable (ordered-even-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ordered-even-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that modifies the blockchain is @('commit-anchors').
     All the other events leave the blockchain unchanged,
     and it is thus easy to prove that they preserve the invariant.")
   (xdoc::p
    "For @('commit-anchors') event,
     we need to assume a previously proved invariant,
     namely @(see last-blockchain-round).
     We use previously proved theorems about
     @(tsee extend-blockchain) and @(tsee collect-anchors).
     We also need to open up @(tsee commit-anchors-possiblep),
     to expose certain needed constraints on the involved round numbers.
     The @(tsee last-blockchain-round-p) assumption
     serves to tie the last committed round in the validator state
     to the round of the newest block of the blockchain
     prior to the addition of the new blocks,
     to complete the relieving of the hypotheses
     of the aforementioned theorems
     about @(tsee extend-blockchain) and @(tsee collect-anchors)."))

  (defruled ordered-even-p-of-create-certificate-next
    (implies (ordered-even-p systate)
             (ordered-even-p (create-certificate-next cert systate)))
    :enable (ordered-even-p
             ordered-even-p-necc
             validator-state->blockchain-of-create-certificate-next
             certificate->round-of-certificate-with-author+round))

  (defruled ordered-even-p-of-receive-certificate-next
    (implies (and (ordered-even-p systate)
                  (receive-certificate-possiblep msg systate))
             (ordered-even-p (receive-certificate-next msg systate)))
    :enable (ordered-even-p
             ordered-even-p-necc
             validator-state->blockchain-of-receive-certificate-next))

  (defruled ordered-even-p-of-store-certificate-next
    (implies (and (ordered-even-p systate)
                  (store-certificate-possiblep val cert systate))
             (ordered-even-p (store-certificate-next val cert systate)))
    :enable (ordered-even-p
             ordered-even-p-necc
             validator-state->blockchain-of-store-certificate-next))

  (defruled ordered-even-p-of-advance-round-next
    (implies (and (ordered-even-p systate)
                  (advance-round-possiblep val systate))
             (ordered-even-p (advance-round-next val systate)))
    :enable (ordered-even-p
             ordered-even-p-necc
             validator-state->blockchain-of-advance-round-next))

  (defruled ordered-even-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (commit-anchors-possiblep val systate))
             (ordered-even-p (commit-anchors-next val systate)))
    :enable (ordered-even-p
             ordered-even-p-necc-fixing
             last-blockchain-round-p-necc-fixing
             validator-state->blockchain-of-commit-anchors-next
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             collect-anchors-above-last-committed-round
             commit-anchors-possiblep
             pos-fix
             posp
             evenp
             certificate->round-of-certificate-with-author+round))

  (defruled ordered-even-p-of-timer-expires-next
    (implies (and (ordered-even-p systate)
                  (timer-expires-possiblep val systate))
             (ordered-even-p (timer-expires-next val systate)))
    :enable (ordered-even-p
             ordered-even-p-necc
             validator-state->blockchain-of-timer-expires-next))

  (defruled ordered-even-p-of-event-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (event-possiblep event systate))
             (ordered-even-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection ordered-even-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled ordered-even-p-of-events-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (events-possiblep events systate))
             (and (ordered-even-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))))
    :induct t
    :disable ((:e tau-system))
    :enable (events-possiblep
             events-next
             ordered-even-p-of-event-next
             last-blockchain-round-p-of-event-next))

  (defruled ordered-even-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (ordered-even-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (ordered-even-p-when-init
             last-blockchain-round-p-when-init
             ordered-even-p-of-events-next)))
