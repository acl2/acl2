; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

(include-book "initialization")
(include-book "transitions")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signed-proposals
  :parents (correctness)
  :short "Proposals signed by validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "An important notion in the protocol is that of
     which proposals have been signed by which validators.
     This concerns not just proposals before they become certificates,
     but also proposals within certificates.
     This notion is used to prove that
     correct signers do not sign equivocal proposals
     (i.e. different proposals with the same author and round),
     which in turn is used to prove that
     correct validators do not have equivocal certificates
     (i.e. different certificates with the same author and round),
     under fault tolerance assumptions.")
   (xdoc::p
    "Here we define the notion of all the proposals,
     in a system state, signed by a given validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props-in-dag ((signer addressp) (dag certificate-setp))
  :returns (props proposal-setp)
  :short "Proposals in a DAG signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to obtain the signed proposals
     from a validator's DAG.")
   (xdoc::p
    "The DAG consists of certificates,
     each of which contains a proposal.
     We collect all the proposals that have the given signer
     as the author or as an endorser."))
  (b* (((when (set::emptyp (certificate-set-fix dag))) nil)
       (cert (set::head dag))
       (props (signed-props-in-dag signer (set::tail dag))))
    (if (or (equal (certificate->author cert)
                   (address-fix signer))
            (set::in (address-fix signer) (certificate->endorsers cert)))
        (set::insert (certificate->proposal cert)
                     props)
      props))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret signed-props-in-dag-subset-dag-props
    (set::subset props (cert-set->prop-set dag))
    :hints (("Goal"
             :induct t
             :in-theory (enable* signed-props-in-dag
                                 cert-set->prop-set
                                 set::expensive-rules)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props-in-proposed ((signer addressp)
                                  (proposed proposal-address-set-mapp))
  :returns (props proposal-setp)
  :short "Proposals in a pending proposal map signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to obtain the signed proposals
     from a validator's pending proposals.")
   (xdoc::p
    "The pending proposals are organized as
     a map from proposals to sets of endorsers,
     which is thus structuraclly isomorphic to a set of certificates.
     We collect all the proposals from the maps
     that have the signer as author or as an endorser.
     As proved in @(see proposed-author-self),
     it is an invariant that all the proposals have the same author,
     namely the validator whose state includes the pending proposals."))
  (b* (((when (omap::emptyp (proposal-address-set-map-fix proposed))) nil)
       ((mv prop endors) (omap::head proposed))
       (props (signed-props-in-proposed signer (omap::tail proposed))))
    (if (or (equal (proposal->author prop)
                   (address-fix signer))
            (set::in (address-fix signer) endors))
        (set::insert prop props)
      props))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret signed-props-in-proposed-subset-keys
    (set::subset props (omap::keys proposed))
    :hints (("Goal"
             :induct t
             :in-theory (enable* signed-props-in-proposed
                                 set::expensive-rules))))

  (defruled in-of-signed-props-in-proposed
    (implies (proposal-address-set-mapp proposed)
             (equal (set::in prop (signed-props-in-proposed signer proposed))
                    (and (omap::assoc prop proposed)
                         (or (equal (address-fix signer)
                                    (proposal->author prop))
                             (set::in (address-fix signer)
                                      (cdr (omap::assoc prop proposed)))))))
    :induct t
    :enable (omap::assoc
             omap::assoc-to-in-of-keys
             set::expensive-rules)
    :disable omap::head-key-not-in-keys-of-tail
    :hints ('(:use (:instance omap::head-key-not-in-keys-of-tail
                              (map proposed)))))

  (defruled signed-props-in-proposed-of-update
    (implies (and (proposalp prop)
                  (address-setp endors)
                  (proposal-address-set-mapp proposed))
             (equal (signed-props-in-proposed
                     signer (omap::update prop endors proposed))
                    (if (or (equal (proposal->author prop)
                                   (address-fix signer))
                            (set::in (address-fix signer)
                                     (address-set-fix endors)))
                        (set::insert prop
                                     (signed-props-in-proposed
                                      signer proposed))
                      (if (and (omap::assoc prop proposed)
                               (set::in (address-fix signer)
                                        (cdr (omap::assoc prop proposed))))
                          (set::delete prop
                                       (signed-props-in-proposed signer
                                                                 proposed))
                        (signed-props-in-proposed signer proposed)))))
    :enable (in-of-signed-props-in-proposed
             set::expensive-rules
             set::double-containment-no-backchain-limit)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props-in-validator ((signer addressp)
                                   (vstate validator-statep))
  :returns (props proposal-setp)
  :short "Proposals in a validator state signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect the ones in the DAG and the ones in the pending map.")
   (xdoc::p
    "We do not need to collect the ones in the @('endorsed') component,
     because the relevant information can be obtained
     from the network (if the endorsement is in transit)
     or from the author
     (if the endorsement has been incorporated
     into the author's pending proposal map).")
   (xdoc::p
    "We do not need to collect the proposals
     in the certificates in the @('committed') component,
     because that component is always a subset of the DAG,
     and is in fact a redundant component, as proved elsewhere."))
  (b* (((validator-state vstate) vstate))
    (set::union (signed-props-in-dag signer vstate.dag)
                (signed-props-in-proposed signer vstate.proposed)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props-in-validators ((signer addressp)
                                    (vals address-setp)
                                    (systate system-statep))
  :guard (set::subset vals (correct-addresses systate))
  :returns (props proposal-setp)
  :short "Proposals in the states of given validators signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect proposals from the states of the given validators."))
  (b* (((when (set::emptyp (address-set-fix vals))) nil)
       (val (set::head vals))
       (props (signed-props-in-validator signer
                                         (get-validator-state val systate)))
       (more-props (signed-props-in-validators signer
                                               (set::tail vals)
                                               systate)))
    (set::union props more-props))
  :prepwork ((local (in-theory (enable emptyp-of-address-set-fix))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable* set::expensive-rules)))
  :hooks (:fix)

  ///

  (defruled signed-props-in-validators-when-assoc-of-proposed
    (implies (and (address-setp vals)
                  (set::in val vals)
                  (proposalp prop)
                  (omap::assoc prop
                               (validator-state->proposed
                                (get-validator-state val systate)))
                  (or (equal signer (proposal->author prop))
                      (set::in signer
                               (cdr (omap::assoc
                                     prop
                                     (validator-state->proposed
                                      (get-validator-state val systate)))))))
             (set::in prop
                      (signed-props-in-validators signer vals systate)))
    :induct t
    :enable (signed-props-in-validator
             in-of-signed-props-in-proposed)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props-in-message ((signer addressp) (msg messagep))
  :returns (props proposal-setp)
  :short "Proposals in a message signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a proposal message,
     we include the proposal if the given signer is the author.
     Although, as proved in @(see proposal-in-author),
     proposals in messages authored by correct validators
     are also in the author's state
     and are therefore collected via @(tsee signed-props-in-validator),
     that is not the case for faulty authors.")
   (xdoc::p
    "For an endorsement message,
     we include the proposal if the given signer is the author or endorser.
     Although, as proved in
     @(see endorsement-in-author) and @(see endorsement-in-endorser),
     the proposal is also in the state of the signer if correct,
     and is thus collected already by @(tsee signed-props-in-validator),
     that is not the case for a faulty signer.")
   (xdoc::p
    "For a certificate message,
     we include the underlying proposal if the given signer is the author.
     Although, as prove in @(see certificate-in-author),
     the certificate (and proposal) is in the DAG of the author if correct,
     and is thus collected already by @(tsee signed-props-in-validator),
     that is not the case for a faulty author.")
   (xdoc::p
    "This function always returns a set with either 0 or 1 elements."))
  (message-case
   msg
   :proposal (if (equal (proposal->author msg.proposal)
                        (address-fix signer))
                 (set::insert msg.proposal nil)
               nil)
   :endorsement (if (or (equal (proposal->author msg.proposal)
                               (address-fix signer))
                        (equal msg.endorser
                               (address-fix signer)))
                    (set::insert msg.proposal nil)
                  nil)
   :certificate (if (equal (certificate->author msg.certificate)
                           (address-fix signer))
                    (set::insert (certificate->proposal msg.certificate)
                                 nil)
                  nil))
  :hooks (:fix)

  ///

  (defret cardinality-of-signed-props-in-message
    (<= (set::cardinality props) 1)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable set::cardinality)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props-in-message-set ((signer addressp) (msgs message-setp))
  :returns (props proposal-setp)
  :short "Proposals in a set of messages signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "We put together all the proposals obtained
     via @(tsee signed-props-in-message) applied to each message in the set."))
  (cond ((set::emptyp (message-set-fix msgs)) nil)
        (t (set::union (signed-props-in-message signer (set::head msgs))
                       (signed-props-in-message-set signer (set::tail msgs)))))
  :prepwork ((local (in-theory (enable emptyp-of-message-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defruled signed-props-in-message-subset-when-in
    (implies (and (message-setp msgs)
                  (set::in msg msgs))
             (set::subset (signed-props-in-message signer msg)
                          (signed-props-in-message-set signer msgs)))
    :induct t
    :enable set::expensive-rules)

  (defruled signed-props-in-message-set-of-insert
    (implies (and (messagep msg)
                  (message-setp msgs))
             (equal (signed-props-in-message-set signer (set::insert msg msgs))
                    (set::union (signed-props-in-message signer msg)
                                (signed-props-in-message-set signer msgs))))
    :induct (set::weak-insert-induction msg msgs)
    :enable (signed-props-in-message-subset-when-in
             set::expensive-rules))

  (defruled signed-props-in-message-set-of-union
    (implies (and (message-setp msgs1)
                  (message-setp msgs2))
             (equal (signed-props-in-message-set signer
                                                 (set::union msgs1 msgs2))
                    (set::union (signed-props-in-message-set signer msgs1)
                                (signed-props-in-message-set signer msgs2))))
    :induct t
    :enable (set::union
             signed-props-in-message-set-of-insert))

  (defruled signed-props-in-message-set-monotone
    (implies (and (message-setp msgs2)
                  (set::subset msgs1 msgs2))
             (set::subset (signed-props-in-message-set signer msgs1)
                          (signed-props-in-message-set signer msgs2)))
    :induct t
    :enable (set::subset
             signed-props-in-message-subset-when-in
             set::expensive-rules))

  (defruled signed-props-in-message-set-of-delete-superset
    (implies (message-setp msgs)
             (set::subset (set::difference
                           (signed-props-in-message-set signer msgs)
                           (signed-props-in-message signer msg))
                          (signed-props-in-message-set
                           signer (set::delete msg msgs))))
    :induct t
    :enable (set::delete
             signed-props-in-message-set-of-insert
             set::expensive-rules))

  (defruled in-of-signed-props-in-message-set-of-delete
    (implies (and (message-setp msgs)
                  (set::in prop (signed-props-in-message-set signer msgs))
                  (not (set::in prop (signed-props-in-message signer msg))))
             (set::in prop (signed-props-in-message-set
                            signer (set::delete msg msgs))))
    :use signed-props-in-message-set-of-delete-superset
    :enable set::expensive-rules
    :disable signed-props-in-message-set)

  (defruled signed-props-in-message-set-of-make-proposal-messages
    (equal (signed-props-in-message-set
            signer (make-proposal-messages prop dests))
           (if (and (equal (address-fix signer)
                           (proposal->author prop))
                    (not (set::emptyp (address-set-fix dests))))
               (set::insert (proposal-fix prop) nil)
             nil))
    :induct t
    :enable (make-proposal-messages
             signed-props-in-message
             signed-props-in-message-set-of-insert
             emptyp-of-address-set-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signed-props ((signer addressp) (systate system-statep))
  :returns (props proposal-setp)
  :short "Proposals in the system signed by a given signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the proposals in all the correct validator's states,
     and the ones in the network.
     While some of the latter are redundant,
     because also contained in correct authors' and endorsers' states,
     others are not redundant, namely the ones signed by faulty validators."))
  (set::union (signed-props-in-validators signer
                                          (correct-addresses systate)
                                          systate)
              (signed-props-in-message-set signer
                                           (get-network-state systate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-when-init
  :short "Initial signed proposals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, all DAGs, all pending proposal maps, and the network
     are empty.
     Thus, there are no signed proposals."))

  (defruled signed-props-in-validators-when-init
    (implies (and (system-initp systate)
                  (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators signer vals systate)
                    nil))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator
             signed-props-in-dag
             signed-props-in-proposed
             system-initp
             system-validators-initp-necc
             validator-init
             set::expensive-rules))

  (defruled signed-props-when-init
    (implies (system-initp systate)
             (equal (signed-props signer systate)
                    nil))
    :enable (signed-props
             signed-props-in-validators-when-init
             signed-props-in-message-set
             system-initp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-propose-next
  :short "How signed proposals change under @('propose') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('propose') event contributes a new proposal
     to the set of proposals signed by the new proposal's author.")
   (xdoc::p
    "If a correct validator creates a proposal,
     it adds it to its map of pending proposals, without ensorsements.
     The validator may also add proposal messages, containing the proposal,
     to the network
     (but there is no requirement to do so: see @(tsee propose-possiblep)).
     In any case, the set of proposals signed by the validator
     is augmented with the new proposal,
     while the set of proposals signed by other validators is unchanged.")
   (xdoc::p
    "If a faulty validator creates a proposal,
     one or more proposal messages, containing the proposal,
     are added to the network;
     @(tsee propose-possiblep) requires at least one such message,
     because otherwise the event would be a no-op in our model.
     Thus, as in the case above of a proposal created by a correct validator,
     the set of proposals signed by the faulty validator
     is augmented with the new proposal,
     while the set of proposals signed by other validators is unchanged."))

  (defruled signed-props-in-validator-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (set::in val (correct-addresses systate)))
             (equal (signed-props-in-validator
                     signer
                     (get-validator-state
                      val (propose-next prop dests systate)))
                    (if (and (equal (address-fix signer)
                                    (proposal->author prop))
                             (equal (address-fix signer)
                                    val))
                        (set::insert (proposal-fix prop)
                                     (signed-props-in-validator
                                      signer
                                      (get-validator-state val systate)))
                      (signed-props-in-validator
                       signer
                       (get-validator-state val systate)))))
    :enable (signed-props-in-validator
             validator-state->proposed-of-propose-next
             signed-props-in-proposed-of-update
             propose-possiblep)
    :prep-lemmas
    ((defrule lemma
       (implies (and (proposal-address-set-mapp proposed)
                     (set::emptyp (props-with-round (proposal->round prop)
                                                    (omap::keys proposed))))
                (not (set::in prop (signed-props-in-proposed signer proposed))))
       :enable (not-in-prop-subset-when-none-with-round
                signed-props-in-proposed-subset-keys
                proposal-setp-of-keys-when-proposal-address-set-mapp))))

  (defruled signed-props-in-validators-of-propose-next
    (implies (and (propose-possiblep prop dests systate)
                  (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (propose-next prop dests systate))
                    (if (and (equal (address-fix signer)
                                    (proposal->author prop))
                             (set::in (address-fix signer) vals)
                             (set::in (address-fix signer)
                                      (correct-addresses systate)))
                        (set::insert (proposal-fix prop)
                                     (signed-props-in-validators
                                      signer vals systate))
                      (signed-props-in-validators signer vals systate))))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-propose-next
             set::expensive-rules))

  (defruled signed-props-of-propose-next
    (implies (propose-possiblep prop dests systate)
             (equal (signed-props signer (propose-next prop dests systate))
                    (if (equal (address-fix signer)
                               (proposal->author prop))
                        (set::insert (proposal-fix prop)
                                     (signed-props signer systate))
                      (signed-props signer systate))))
    :enable (signed-props
             propose-possiblep
             get-network-state-of-propose-next
             signed-props-in-message-set-of-union
             signed-props-in-message-set-of-make-proposal-messages
             signed-props-in-validators-of-propose-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-endorse-next
  :short "How signed proposals change under @('endorse') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('endorse') event contributes the endorsed proposal
     to the set of proposals signed by the endorser.")
   (xdoc::p
    "When a (correct or faulty) validator endorses a proposal,
     it removes a proposal message from the network
     and adds an endorsement message to the network.
     The two messages have the same proposal.
     The proposal message contributes the proposal to
     the set of proposals in the system signed by the proposal's author;
     the endorsement message makes the same contribution,
     but it also contributes the proposal to
     the set of proposals in the system signed by the endorsing validator.
     Thus, the net effect is to add that proposal to
     the set of proposals in the system signed by the endorser,
     and to leave unchanged
     all the sets of proposals signed by other validators.")
   (xdoc::p
    "As proved in @(see endorsement-from-other),
     the endorser always differs from the proposal author
     if the latter is correct,
     but this fact does not affect the formulation of the theorem."))

  (defruled signed-props-in-validator-of-endorse-next
    (implies (set::in val (correct-addresses systate))
             (equal (signed-props-in-validator
                     signer
                     (get-validator-state
                      val (endorse-next prop endor systate)))
                    (signed-props-in-validator
                     signer
                     (get-validator-state val systate))))
    :enable signed-props-in-validator)

  (defruled signed-props-in-validators-of-endorse-next
    (implies (and (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (endorse-next prop endor systate))
                    (signed-props-in-validators
                     signer vals systate)))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-endorse-next
             set::expensive-rules))

  (defruled signed-props-of-endorse-next
    (implies (endorse-possiblep prop endor systate)
             (equal (signed-props signer (endorse-next prop endor systate))
                    (if (equal (address-fix signer)
                               (address-fix endor))
                        (set::insert (proposal-fix prop)
                                     (signed-props signer systate))
                      (signed-props signer systate))))
    :enable (signed-props
             signed-props-in-validators-of-endorse-next
             get-network-state-of-endorse-next
             signed-props-in-message-set-of-insert
             signed-props-in-message
             set::expensive-rules
             endorse-possiblep)
    :use ((:instance signed-props-in-message-set-of-delete-superset
                     (msg (message-proposal prop endor))
                     (msgs (get-network-state systate)))
          (:instance signed-props-in-message-set-monotone
                     (msgs1 (set::delete (message-proposal prop endor)
                                         (get-network-state systate)))
                     (msgs2 (get-network-state systate)))
          (:instance signed-props-in-message-subset-when-in
                     (msg (message-proposal prop endor))
                     (msgs (get-network-state systate))))))
