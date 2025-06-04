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

(include-book "initialization")
(include-book "transitions")

(local (include-book "../library-extensions/omap-theorems"))

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
     in a system state, signed by a given validator.
     We also prove theorems saying
     what this operation returns in initial states
     and how the result of this operation changes under events."))
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
    (if (set::in (address-fix signer)
                 (certificate->signers cert))
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
                                 set::expensive-rules))))

  (defruled in-signed-props-in-dag-when-in-dag-and-signer
    (implies (and (certificate-setp dag)
                  (set::in cert dag)
                  (set::in (address-fix signer)
                           (certificate->signers cert)))
             (set::in (certificate->proposal cert)
                      (signed-props-in-dag signer dag)))
    :induct t)

  (defruled signed-props-in-dag-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp dag))
             (equal (signed-props-in-dag signer (set::insert cert dag))
                    (if (set::in (address-fix signer)
                                 (certificate->signers cert))
                        (set::insert (certificate->proposal cert)
                                     (signed-props-in-dag signer dag))
                      (signed-props-in-dag signer dag))))
    :induct (set::weak-insert-induction cert dag)
    :enable in-signed-props-in-dag-when-in-dag-and-signer))

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
             set::double-containment-no-backchain-limit))

  (defruled signed-props-in-proposed-of-delete-superset
    (set::subset (set::delete prop
                              (signed-props-in-proposed signer proposed))
                 (signed-props-in-proposed signer
                                           (omap::delete prop proposed)))
    :induct t
    :enable (signed-props-in-proposed
             omap::assoc
             in-of-signed-props-in-proposed
             set::expensive-rules))

  (defruled in-of-signed-props-in-proposed-of-delete
    (implies (and (set::in prop1 (signed-props-in-proposed signer proposed))
                  (not (equal prop1 prop)))
             (set::in prop1
                      (signed-props-in-proposed
                       signer (omap::delete prop proposed))))
    :use signed-props-in-proposed-of-delete-superset
    :enable set::expensive-rules
    :disable signed-props-in-proposed)

  (defruled signed-props-in-proposed-monotone
    (implies (and (proposal-address-set-mapp proposed2)
                  (omap::submap proposed1 proposed2))
             (set::subset (signed-props-in-proposed signer proposed1)
                          (signed-props-in-proposed signer proposed2)))
    :induct t
    :enable (omap::submap
             in-of-signed-props-in-proposed)))

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

  (defruled prop-in-signed-props-in-validators-when-assoc-of-proposed
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
   :certificate (if (set::in (address-fix signer)
                             (certificate->signers msg.certificate))
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
             emptyp-of-address-set-fix))

  (defruled signed-props-in-message-set-of-make-certificate-messages
    (equal (signed-props-in-message-set
            signer (make-certificate-messages cert dests))
           (if (and (set::in (address-fix signer)
                             (certificate->signers cert))
                    (not (set::emptyp (address-set-fix dests))))
               (set::insert (certificate->proposal cert) nil)
             nil))
    :induct t
    :enable (make-certificate-messages
             signed-props-in-message
             signed-props-in-message-set-of-insert
             emptyp-of-address-set-fix))

  (defruled in-signed-props-in-message-set-when-message-endorsement
    (implies (and (proposalp prop)
                  (message-setp msgs)
                  (set::in (message-endorsement prop endor) msgs)
                  (or (equal (address-fix signer)
                             (proposal->author prop))
                      (equal (address-fix signer)
                             (address-fix endor))))
             (set::in prop (signed-props-in-message-set signer msgs)))
    :induct t
    :enable signed-props-in-message)

  (defruled in-signed-props-in-message-set-when-make-endorsement-messages
    (implies (and (proposalp prop)
                  (message-setp msgs)
                  (not (set::emptyp (address-set-fix endors)))
                  (set::subset (make-endorsement-messages prop endors) msgs)
                  (or (equal (address-fix signer)
                             (proposal->author prop))
                      (set::in (address-fix signer)
                               (address-set-fix endors))))
             (set::in prop (signed-props-in-message-set signer msgs)))
    :induct t
    :disable signed-props-in-message-set
    :enable (make-endorsement-messages
             emptyp-of-address-set-fix
             in-signed-props-in-message-set-when-message-endorsement))

  (defruled in-signed-props-in-message-set-when-message-certificate
    (implies (and (message-setp msgs)
                  (set::in (message-certificate cert dest) msgs)
                  (set::in (address-fix signer)
                           (certificate->signers cert)))
             (set::in (certificate->proposal cert)
                      (signed-props-in-message-set signer msgs)))
    :induct t
    :enable signed-props-in-message)

  (defruled in-signed-props-in-message-set-when-make-certificate-messages
    (implies (and (message-setp msgs)
                  (not (set::emptyp (address-set-fix dests)))
                  (set::subset (make-certificate-messages cert dests) msgs)
                  (set::in (address-fix signer)
                           (certificate->signers cert)))
             (set::in (certificate->proposal cert)
                      (signed-props-in-message-set signer msgs)))
    :induct t
    :disable signed-props-in-message-set
    :enable (make-certificate-messages
             in-signed-props-in-message-set-when-message-certificate)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-augment-next
  :short "How signed proposals change under @('augment') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('augment') event does not change
     the set of proposals signed by each validator.")
   (xdoc::p
    "The event removes an endorsement message from the network,
     which contributes the proposal to the sets of proposals signed by
     the proposal's author and the endorser in the message.
     But the event can only happen if the proposal author is correct,
     and if its pending proposal map includes that proposal.
     The event leaves the proposal in the map,
     and adds the new endorser.
     Thus, the map contributes the same proposals as the message."))

  (defruled signed-props-in-validator-of-augment-next
    (implies (augment-possiblep prop endor systate)
             (equal (signed-props-in-validator
                     signer
                     (get-validator-state
                      val (augment-next prop endor systate)))
                    (if (and (equal (address-fix val)
                                    (proposal->author prop))
                             (equal (address-fix signer)
                                    (address-fix endor)))
                        (set::insert (proposal-fix prop)
                                     (signed-props-in-validator
                                      signer
                                      (get-validator-state val systate)))
                      (signed-props-in-validator
                       signer
                       (get-validator-state val systate)))))
    :enable (signed-props-in-validator
             validator-state->proposed-of-augment-next
             augment-possiblep
             signed-props-in-proposed-of-update
             in-of-signed-props-in-proposed
             omap::lookup))

  (defruled signed-props-in-validators-of-augment-next
    (implies (and (augment-possiblep prop endor systate)
                  (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (augment-next prop endor systate))
                    (if (and (set::in (proposal->author prop) vals)
                             (equal (address-fix signer)
                                    (address-fix endor)))
                        (set::insert (proposal-fix prop)
                                     (signed-props-in-validators
                                      signer vals systate))
                      (signed-props-in-validators signer vals systate))))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-augment-next
             set::expensive-rules))

  (defrule signed-props-of-augment-next
    (implies (augment-possiblep prop endor systate)
             (equal (signed-props signer (augment-next prop endor systate))
                    (signed-props signer systate)))
    :enable (set::double-containment-no-backchain-limit
             set::expensive-rules)

    :prep-lemmas

    ((defrule lemma1
       (implies (augment-possiblep prop endor systate)
                (implies (set::in x (signed-props
                                     signer (augment-next prop endor systate)))
                         (set::in x (signed-props signer systate))))
       :enable (signed-props
                signed-props-in-validators-of-augment-next
                get-network-state-of-augment-next
                augment-possiblep
                signed-props-in-message
                set::expensive-rules)
       :use ((:instance signed-props-in-message-set-monotone
                        (msgs1 (set::delete (message-endorsement prop endor)
                                            (get-network-state systate)))
                        (msgs2 (get-network-state systate)))
             (:instance signed-props-in-message-subset-when-in
                        (msg (message-endorsement prop endor))
                        (msgs (get-network-state systate)))))

     (defrule lemma2
       (implies (augment-possiblep prop endor systate)
                (implies (set::in x (signed-props signer systate))
                         (set::in x (signed-props
                                     signer
                                     (augment-next prop endor systate)))))
       :enable (signed-props
                signed-props-in-validators-of-augment-next
                get-network-state-of-augment-next
                augment-possiblep
                signed-props-in-message
                set::expensive-rules)
       :use ((:instance in-of-signed-props-in-message-set-of-delete
                        (msgs (get-network-state systate))
                        (prop x)
                        (msg (message-endorsement prop endor)))
             (:instance
              prop-in-signed-props-in-validators-when-assoc-of-proposed
              (vals (correct-addresses systate))
              (val (address-fix signer))
              (signer (address-fix signer))
              (prop (proposal-fix prop))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-certify-next
  :short "How signed proposals change under @('certify') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('certify') event almost never changes
     the set of proposals signed by each validator,
     except when the certificate author is faulty
     and the certificate has no endorsements:
     in this case, the proposal in the certificate is added to
     the set of proposals signed by the author.")
   (xdoc::p
    "When the author is correct,
     its pending proposal map must contain
     the proposal and the endorsements that form the certificate.
     The entry is removed from the map,
     but the certificate is added to the author's DAG,
     and thus there is no change to the set of proposals
     signed by the certificate's signers (author and endorsers)
     as far as validator states are concerned.
     The addition of certificate messages to the network
     does not contribute any new proposal to those signed sets.")
   (xdoc::p
    "If the author is faulty,
     but the certificate has at least one endorser,
     then there must be at least one endorsement message in the network,
     which contributes the proposal to
     the set of proposals signed by the author
     and the set of proposals signed by the endorser.
     In fact, every endorsers of the certificate
     must have a corresponding endorsing message.
     The endorsing messages are not removed from the network;
     thus the generated certificate messages do not contribute new proposals.
     However, if the certificate has no endorsers,
     then there may be no endorsement messages;
     the event can happen only if at least one certificate message is sent,
     which contributes the proposal in the certificate
     to the set of proposals signed by the author.
     So this is the only case in which a new proposal
     may be added to the sets of signed proposals.
     Note that the addition may be a no-op, in case, for example,
     there are in fact endorsement messages in the network,
     but the faulty validators nondeterministically
     chooses to not use any of them."))

  (defruled signed-props-in-validator-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (set::in val (correct-addresses systate)))
             (equal (signed-props-in-validator
                     signer
                     (get-validator-state
                      val (certify-next cert dests systate)))
                    (signed-props-in-validator
                     signer (get-validator-state val systate))))
    :enable (signed-props-in-validator
             validator-state->dag-of-certify-next
             validator-state->proposed-of-certify-next
             signed-props-in-dag-of-insert
             in-of-signed-props-in-proposed
             certify-possiblep
             certificate->author
             certificate->signers
             set::expensive-rules))

  (defruled signed-props-in-validators-of-certify-next
    (implies (and (certify-possiblep cert dests systate)
                  (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (certify-next cert dests systate))
                    (signed-props-in-validators signer vals systate)))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-certify-next
             set::expensive-rules))

  (defruled signed-props-of-certify-next
    (implies (certify-possiblep cert dests systate)
             (equal (signed-props signer (certify-next cert dests systate))
                    (if (and (not (set::in (certificate->author cert)
                                           (correct-addresses systate)))
                             (equal (address-fix signer)
                                    (certificate->author cert))
                             (set::emptyp (certificate->endorsers cert)))
                        (set::insert (certificate->proposal cert)
                                     (signed-props signer systate))
                      (signed-props signer systate))))
    :use (lemma-correct lemma-faulty)

    :prep-lemmas

    ((defruled lemma-correct
       (implies (and (certify-possiblep cert dests systate)
                     (set::in (certificate->author cert)
                              (correct-addresses systate)))
                (equal (signed-props signer (certify-next cert dests systate))
                       (signed-props signer systate)))
       :enable (signed-props
                signed-props-in-validators-of-certify-next
                get-network-state-of-certify-next
                signed-props-in-message-set-of-union
                signed-props-in-message-set-of-make-certificate-messages
                certify-possiblep
                certificate->author
                certificate->signers)
       :use (:instance prop-in-signed-props-in-validators-when-assoc-of-proposed
                       (vals (correct-addresses systate))
                       (val (certificate->author cert))
                       (prop (certificate->proposal cert))
                       (signer (address-fix signer))))

     (defruled lemma-faulty
       (implies (and (certify-possiblep cert dests systate)
                     (not (set::in (certificate->author cert)
                                   (correct-addresses systate))))
                (equal (signed-props signer (certify-next cert dests systate))
                       (if (and (equal (address-fix signer)
                                       (certificate->author cert))
                                (set::emptyp (certificate->endorsers cert)))
                           (set::insert (certificate->proposal cert)
                                        (signed-props signer systate))
                         (signed-props signer systate))))
       :enable (signed-props
                signed-props-in-validators-of-certify-next
                get-network-state-of-certify-next
                signed-props-in-message-set-of-union
                signed-props-in-message-set-of-make-certificate-messages
                certify-possiblep
                certificate->signers
                certificate->author)
       :use (:instance
             in-signed-props-in-message-set-when-make-endorsement-messages
             (prop (certificate->proposal cert))
             (msgs (get-network-state systate))
             (endors (certificate->endorsers cert)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-accept-next
  :short "How signed proposals change under @('accept') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('accept') event does not change
     the set of proposals signed by any validator.")
   (xdoc::p
    "This event only involves correct validators.
     A certificate message is removed from the network,
     but the certificate is added to the DAG of the validator.
     Thus, there two changes compensate each other,
     for every signer (author and endorser) of the certificate."))

  (defruled signed-props-in-validator-of-accept-next
    (implies (accept-possiblep val cert systate)
             (equal (signed-props-in-validator
                     signer
                     (get-validator-state
                      val1 (accept-next val cert systate)))
                    (if (and (equal (address-fix val1)
                                    (address-fix val))
                             (set::in (address-fix signer)
                                      (certificate->signers cert)))
                        (set::insert (certificate->proposal cert)
                                     (signed-props-in-validator
                                      signer
                                      (get-validator-state val1 systate)))
                      (signed-props-in-validator
                       signer (get-validator-state val1 systate)))))
    :enable (signed-props-in-validator
             validator-state->dag-of-accept-next
             signed-props-in-dag-of-insert
             accept-possiblep))

  (defruled signed-props-in-validators-of-accept-next
    (implies (and (accept-possiblep val cert systate)
                  (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (accept-next val cert systate))
                    (if (and (set::in (address-fix val) vals)
                             (set::in (address-fix signer)
                                      (certificate->signers cert)))
                        (set::insert (certificate->proposal cert)
                                     (signed-props-in-validators
                                      signer vals systate))
                      (signed-props-in-validators signer vals systate))))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-accept-next
             set::expensive-rules))

  (defrule signed-props-of-accept-next
    (implies (accept-possiblep val cert systate)
             (equal (signed-props signer (accept-next val cert systate))
                    (signed-props signer systate)))
    :enable (signed-props
             signed-props-in-validators-of-accept-next
             get-network-state-of-accept-next
             in-of-signed-props-in-message-set-of-delete
             signed-props-in-message
             accept-possiblep
             signed-props-in-message-set-monotone
             in-signed-props-in-message-set-when-message-certificate
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-advance-next
  :short "How signed proposals change under @('advance') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "An @('advance') event does not change
     the set of proposals signed by any validator.")
   (xdoc::p
    "This event does not change DAGs, pending proposal maps, or the network;
     thus, there is no change to the sets of signer proposals."))

  (defruled signed-props-in-validator-of-advance-next
    (equal (signed-props-in-validator
            signer
            (get-validator-state val1 (advance-next val systate)))
           (signed-props-in-validator
            signer
            (get-validator-state val1 systate)))
    :enable signed-props-in-validator)

  (defruled signed-props-in-validators-of-advance-next
    (implies (and (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (advance-next val systate))
                    (signed-props-in-validators signer vals systate)))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-advance-next
             set::expensive-rules))

  (defrule signed-props-of-advance-next
    (implies (advance-possiblep val systate)
             (equal (signed-props signer (advance-next val systate))
                    (signed-props signer systate)))
    :enable (signed-props
             signed-props-in-validators-of-advance-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signed-props-of-commit-next
  :short "How signed proposals change under @('commit') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('commit') event does not change
     the set of proposals signed by any validator.")
   (xdoc::p
    "This event does not change DAGs, pending proposal maps, or the network;
     thus, there is no change to the sets of signer proposals."))

  (defruled signed-props-in-validator-of-commit-next
    (equal (signed-props-in-validator
            signer
            (get-validator-state val1 (commit-next val systate)))
           (signed-props-in-validator
            signer
            (get-validator-state val1 systate)))
    :enable signed-props-in-validator)

  (defruled signed-props-in-validators-of-commit-next
    (implies (and (address-setp vals)
                  (set::subset vals (correct-addresses systate)))
             (equal (signed-props-in-validators
                     signer vals (commit-next val systate))
                    (signed-props-in-validators signer vals systate)))
    :induct t
    :enable (signed-props-in-validators
             signed-props-in-validator-of-commit-next
             set::expensive-rules))

  (defrule signed-props-of-commit-next
    (implies (commit-possiblep val systate)
             (equal (signed-props signer (commit-next val systate))
                    (signed-props signer systate)))
    :enable (signed-props
             signed-props-in-validators-of-commit-next)))
