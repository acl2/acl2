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
  :hooks (:fix))

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
  :hooks (:fix))

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
  :hooks (:fix))

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
  :hooks (:fix))

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
  :short "Initially there are no signed proposals."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, all DAGs, all pending proposal maps, and the network
     are empty."))

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
