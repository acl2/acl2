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

(include-book "ordered-even-blocks")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dag-committees
  :parents (correctness)
  :short "Invariant that every author of every certificate in every DAG
          is a member of the active committee for that round,
          which the validator can calculate."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created via @('create'),
     the author must know the active committee at the certificate's round,
     which it uses to check quorum conditions;
     these conditions include the fact that
     the author is a member of that committee.")
   (xdoc::p
    "When a certificate is stored via @('store'),
     the validator must know the active committee at the certificate's round,
     which it uses to check quorum conditions;
     these conditions include the fact that
     the author of the certificate is a member of that committee.")
   (xdoc::p
    "The above events are the only ones that extend DAGs.
     Thus, it is the case that the active committee
     at the round of each certificate in the DAG of a validator
     is known to (i.e. calculable by) the validator,
     and that the author of that certificate is in that committee."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-committees-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every certificate in the DAG of a validator,
          the validator can calculate the active committee
          at the round of the certificate,
          and the certificate's author is a member of the that committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is expressed via two predicates on DAGs."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (b* (((validator-state vstate)
                         (get-validator-state val systate)))
                     (and (dag-has-committees-p vstate.dag vstate.blockchain)
                          (dag-in-committees-p vstate.dag vstate.blockchain)))))
  ///
  (fty::deffixequiv-sk dag-committees-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-committees-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially all DAGs are empty,
     so the needed conditions trivially hold."))
  (implies (system-initp systate)
           (dag-committees-p systate))
  :enable (dag-committees-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dag-committees-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "For @('create') and @('store'), which may extend DAGs,
     we open @(tsee create-possiblep) and @(tsee store-possiblep)
     to expose the fact that the validator
     can calculate the committee at the round
     of the created or stored certificate,
     and that the certificate's author, being part of the quorum of signers,
     is a member of that committee.
     For certificates already in the DAG,
     the ability to calculate the committee,
     and the membership of the certificate's author in the committee,
     follows from the assumption of the invariant
     in the state before the transition.")
   (xdoc::p
    "The other events do not change the DAGs or blockchains,
     but @('commit') changes the blockchain of the target validator.
     However, it extends it, and thus the previously calculated committee
     can be still calculated with the extended blockchain,
     and do not change, so their members do not change.
     The main rule used for this is
     @('active-committee-at-round-of-extend-blockchain-no-change'),
     along with others to relieve its hypotheses.
     Note that we need to assume some previously proved invariants
     about blocks having even ordered round,
     and about the relation between the round of the latest block."))

  (defruled dag-committees-p-of-create-next
    (implies (and (dag-committees-p systate)
                  (create-possiblep cert systate))
             (dag-committees-p (create-next cert systate)))
    :enable (dag-committees-p
             dag-has-committees-p-of-insert
             dag-in-committees-p-of-insert
             dag-committees-p-necc
             validator-state->dag-of-create-next
             create-possiblep
             create-author-possiblep
             create-signer-possiblep))

  (defruled dag-committees-p-of-receive-next
    (implies (and (dag-committees-p systate)
                  (receive-possiblep msg systate))
             (dag-committees-p (receive-next msg systate)))
    :enable (dag-committees-p
             dag-committees-p-necc))

  (defruled dag-committees-p-of-store-next
    (implies (and (dag-committees-p systate)
                  (store-possiblep val cert systate)
                  (addressp val))
             (dag-committees-p (store-next val cert systate)))
    :enable (dag-committees-p
             dag-has-committees-p-of-insert
             dag-in-committees-p-of-insert
             dag-committees-p-necc
             validator-state->dag-of-store-next
             store-possiblep
             certificate->signers))

  (defruled dag-committees-p-of-advance-next
    (implies (and (dag-committees-p systate)
                  (advance-possiblep val systate))
             (dag-committees-p (advance-next val systate)))
    :enable (dag-committees-p
             dag-committees-p-necc))

  (defruled dag-committees-p-of-commit-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (dag-committees-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (dag-committees-p (commit-next val systate)))
    :expand (dag-committees-p (commit-next val systate))
    :enable (dag-committees-p-necc
             validator-state->blockchain-of-commit-next
             dag-has-committees-p-of-extend-blockchain
             dag-in-committees-p-of-extend-blockchain
             commit-possiblep
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             ordered-even-p-necc
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             evenp))

  (defruled dag-committees-p-of-timeout-next
    (implies (and (dag-committees-p systate)
                  (timeout-possiblep val systate))
             (dag-committees-p (timeout-next val systate)))
    :enable (dag-committees-p
             dag-committees-p-necc))

  (defruled dag-committees-p-of-event-next
    (implies (and (dag-committees-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (event-possiblep event systate))
             (dag-committees-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dag-committees-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled dag-committees-p-of-events-next
    (implies (and (dag-committees-p systate)
                  (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (events-possiblep events systate))
             (and (dag-committees-p (events-next events systate))
                  (ordered-even-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))))
    :induct t
    :enable (events-possiblep
             events-next))

  (defruled dag-committees-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (dag-committees-p (events-next events systate)))))
