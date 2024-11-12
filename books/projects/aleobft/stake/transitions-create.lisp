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

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-create
  :parents (transitions)
  :short "Transitions for certificate creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('create') events.")
   (xdoc::p
    "In AleoBFT, certificates are created through an exchange of messages
     involving proposals, signatures, and certificates,
     following the Narwhal protocol, which AleoBFT is based on.
     Currently we model certificate creation as one atomic event,
     which abstracts the aforementioned message exchange process.
     Our @('create') event ``instantly'' creates a certificates,
     and broadcasts it to the other validators.
     This can be thought of as modeling the final act of
     the aforementioned message exchange,
     namely the creation and broadcasting of the certificates
     after proposals and signatures have been exchanged,
     with the exchange of proposals and signatures
     not being explicitly modeled.")
   (xdoc::p
    "Modeling certificate creation as an atomic event
     on the one hand simplifies things,
     because there are fewer events and messages to consider,
     but on the other hand makes the definition of
     the certificate creation transitions slightlly more complicated,
     because we need to model things related to
     not only the actual certificate creation,
     but also the (implicit) exchange of proposals and signatures.")
   (xdoc::p
    "This modeling of certificate creation is not ideal, but adequate for now.
     We plan to develop, in the future, a model of AleoBFT that explicates
     the exchange of proposals, signatures, and certificates.")
   (xdoc::p
    "Because of this atomic modeling of certificate creation,
     a certificate creation transition involves multiple validators,
     namely author and endorsers;
     it also involves the network component of the system state.
     In contrast, all other events involve just one validator."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-signer-possiblep ((cert certificatep) (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of a correct signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is a signer of the certificate.
     See the (indirect) callers of this function.")
   (xdoc::p
    "A certificate is signed by author and endorsers,
     so the signers are the author and the endorsers;
     see @(tsee certificate->signers).
     A correct (i.e. non-faulty) signer, whether author or endorser,
     signs a certificate only if certain conditions are met;
     these conditions are checked against the signer's state.
     This ACL2 function formalizes the conditions
     that are common to author and endorsers, i.e. signers in general.
     Further conditions for the author are
     formalized in @(tsee create-author-possiblep);
     further conditions for the endorsers are
     formalized in @(tsee create-endorser-possiblep).")
   (xdoc::p
    "First, the signer must be able to calculate
     the active committee at the certificate's round.
     That is, its local blockchain must be sufficiently far along.
     If the validator cannot calculate the active committee,
     it is unable to author or endorse a certificate for that round,
     so this event cannot happen from the point of view of the validator.")
   (xdoc::p
    "Both author and endorsers must be in the active committee,
     and must be distinct from each other.
     If the signer is the author, it directly enforces these conditions,
     before broadcasting the certificate.
     If the signer is an endorser, it initially only sees the proposal,
     which does not include the other endorsers,
     so it would be possible that a faulty author
     may send a good proposal but a bad certificate for the proposal.
     However, it must be kept in mind that,
     besides endorsers checking proposals,
     validators also check certificates as they realize
     the reliable broadcast mechanism that our model assumes.
     Thus a bad certificate would not correspond to
     a @('create') event in our model,
     which involves reliable broadcast.
     This is a somewhat complex and perhaps not fully persuasive aspect
     of our current formalization of atomic certificate creation,
     but we plan to develop a more refined model
     with explcit proposals, signatures, and checks on certificates,
     which should clarify this aspect of AleoBFT.")
   (xdoc::p
    "The total stake of the signers must be
     at least the quorum stake of the committee.
     This is the proper generalization to stake
     of the analogous condition on number of validators.
     For the latter, the condition is
     equality between the number of signers and the quorum number.
     With stake, the granularity is a whole validator (it either signs or not),
     and the total stake may not be exactly equal to the quorum stake,
     because the signers may have arbitrary amounts of stake.
     So the proper condition with stake is that
     the quorum stake is an (inclusive) lower bound.")
   (xdoc::p
    "The DAG of the signer must not already have
     a certificate with the given author and round.
     This is to prevent equivocation, i.e. the existence of
     two different certificates with the same author and round.
     Further conditions about this apply to endorsers,
     but here we are defining conditions common to author and endorsers.")
   (xdoc::p
    "If the round of the certificate is 1,
     it must have no references to previous certificates,
     because there is no round 0.
     If the round of the certificate is not 1,
     the following two additional requirements apply.")
   (xdoc::p
    "The signer's DAG must include
     all the previous certificates referenced by the certificate.
     These are the certificates at the round just before the certificate's round
     whose authors are in the @('previous') component of the certificate.
     We express this condition by saying that
     the authors of all the certificates at the round before the certificate
     are a superset of the authors in the @('previous') component.
     When the signer is the author,
     this condition corresponds to the fact that,
     before authoring a certificate,
     the validator must have enough predecessors,
     which the new certificate references.
     When the signer is an endorser,
     this condition corresponds to the fact that,
     before endorsing a certificate from another validator,
     a validator checks it against the predecessors
     (something not explicit in our current model),
     and therefore the validator must have those predecessors in the DAG.")
   (xdoc::p
    "The total stake of the certificate referenced in the previous round
     must be at least the committee quorum stake.
     Similarly to the condition on the stake of the signers,
     this is the proper generalization from numbers of validators to stake.
     Note that the active committee of the previous round
     may differ from the one of the certificate's round.
     Since we already checked that the active committee of the certificate round
     is known to the signer whose conditions we are checking,
     it follows that the active committee at the previous round is also known,
     as proved in @(tsee active-committee-at-round).
     It is an invariant, proved elsewhere,
     that the authors of the certificates in the previous round
     that are referenced in the @('previous') component of @('cert')
     are members of the active committee at that previous round;
     however, this invariant is not available in this definiion here,
     and so we add that as an additional check,
     which is in fact superfluous assuming that invariant."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       (commtt (active-committee-at-round cert.round vstate.blockchain))
       ((unless commtt)
        nil)
       ((when (set::in cert.author cert.endorsers)) nil)
       ((unless (set::in cert.author (committee-members commtt)))
        nil)
       ((unless (set::subset cert.endorsers (committee-members commtt)))
        nil)
       ((unless (>= (committee-members-stake (certificate->signers cert) commtt)
                    (committee-quorum-stake commtt)))
        nil)
       ((when (certificate-with-author+round cert.author cert.round vstate.dag))
        nil)
       ((when (= cert.round 1))
        (set::emptyp cert.previous))
       ((unless (set::subset cert.previous
                             (certificate-set->author-set
                              (certificates-with-round (1- cert.round)
                                                       vstate.dag))))
        nil)
       (prev-commtt
        (active-committee-at-round (1- cert.round) vstate.blockchain))
       ((unless (set::subset cert.previous
                             (committee-members prev-commtt)))
        nil)
       ((unless (>= (committee-members-stake cert.previous prev-commtt)
                    (committee-quorum-stake prev-commtt)))
        nil))
    t)
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       certificate->signers
                       active-committee-at-previous-round-when-at-round)))
  :hooks (:fix)

  ///

  (defruled active-committee-at-round-when-create-signer-possiblep
    (implies (create-signer-possiblep cert vstate)
             (active-committee-at-round (certificate->round cert)
                                        (validator-state->blockchain vstate)))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-author-possiblep ((cert certificatep) (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of a correct author."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is the certificate's author.
     See the (indirect) callers of this function.")
   (xdoc::p
    "In addition to the conditions
     formalized in @(tsee create-signer-possiblep),
     a correct validator authors a certificate
     if additional conditions are satisfied.
     This function puts these additional conditions
     together with the conditions in that function.")
   (xdoc::p
    "The round of the certificate must be the current round of the validator.
     A correct validator only creates (at most) one certificate per round,
     and does so for the current round every time.")
   (xdoc::p
    "That is the only additional condition.
     A correct validator only authors a certificate
     if the validator is in the active committee for that round,
     but @(tsee create-signer-possiblep)
     already checks that the certificate author is in the committee.
     The other conditions in @(tsee create-signer-possiblep)
     are naturally checked by the certificate's author,
     who is in charge of creating the certificate."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       ((unless (create-signer-possiblep cert vstate))
        nil)
       ((unless (= cert.round vstate.round))
        nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-endorser-possiblep ((cert certificatep)
                                   (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of a correct endorser."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is an endorser of the certificate.
     See the (indirect) callers of this function.")
   (xdoc::p
    "In addition to the conditions
     formalized in @(tsee create-signer-possiblep),
     a correct validator endorses a certificate
     if additional conditions are satisfied.
     This function puts these additional conditions
     together with the conditions of that function.")
   (xdoc::p
    "While @(tsee create-signer-possiblep) checks that
     the DAG has no certificate already with the same author and round,
     which is sufficient for the author to check,
     an endorser must also check that
     the set of endorsed author-round pairs
     does not already contain the author-round pair of the certificate.
     The presence of a pair in this set indicates that the validator
     has already endorsed a certificate with that author and round,
     but has not yet received the actual certificate from the network,
     and incorporated it into its own DAG.
     This check is not needed for the signer,
     because it is an invariant, proved elsewhere,
     that the set of endorsed author-round pairs
     does not contain any pair with the validator as author.")
   (xdoc::p
    "Note that, unlike in our previous model
     with dynamic committees but without stake,
     here we are not checking that
     the buffer does not contain a certificate
     with the same author and round as @('cert').
     This difference has nothing to do with stake:
     we are simply experimenting with a slightly different modeling approach,
     in which we let the buffer accept any certificate from the network,
     but we make certain additional checks before storing it into the DAG;
     those additional checks,
     in the model with dynamic committees without stake,
     are performed as part of the event
     to receive a certificate from the network.
     Both in that and in this model of AleoBFT,
     nothing prevents the creation and broadcast of a certificate
     that is signed by only faulty validators
     and that has the same author and round of
     some existing certificate in the DAGs of correct validators.
     In the model without stake,
     that certificate will stay forever in the network,
     never moved to any correct validator's buffer,
     because the event to receive the certificate
     can only happen (because we model it that way)
     if the signers are in the appropriate committee,
     which must be fault-tolerant by assumption.
     But in this model with stake,
     we let any certificate to be received,
     and instead move that committee check
     to the event that moves the certificate from the buffer to the DAG."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       ((unless (create-signer-possiblep cert vstate))
        nil)
       ((when (set::in (make-address+pos :address cert.author :pos cert.round)
                       vstate.endorsed))
        nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-endorsers-possiblep ((cert certificatep)
                                    (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of all the certificate's endorsers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).")
   (xdoc::p
    "An endorser may be correct or faulty.
     If it is correct, it must satisfy the conditions
     formalized in @(tsee create-endorser-possiblep).
     If it is faulty, it is not bound by any condition.")
   (xdoc::p
    "Note that, if there are (as normal) multiple correct endorsers,
     the conditions involving committees as viewed by the endorsers,
     and checked by this predicate,
     imply at least some agreement among the blockchains of the validators,
     enough to make consistent checks involving the committee.
     As proved elsewhere,
     it is a system invariant that
     different validators agree on the committees they can both calculate,
     because of the invariant that blockchains never fork.
     Thus, in each state, which satisfies the invariant,
     starting with an initial state,
     the conditions on the possibility of a @('create') event
     do not impose any more agreement requirements
     than already implied by the invariants.
     As already observed in @(tsee create-signer-possiblep),
     all of this can be made even more clear and persuasive
     in a planned more detailed model of AleoBFT
     that includes explicit proposal and signature exchanges."))
  (create-endorsers-possiblep-loop cert
                                   (certificate->endorsers cert)
                                   systate)
  :hooks (:fix)

  :prepwork
  ((define create-endorsers-possiblep-loop ((cert certificatep)
                                            (endorsers address-setp)
                                            (systate system-statep))
     :returns (yes/no booleanp)
     :parents nil
     (b* (((when (set::emptyp endorsers)) t)
          (endorser (set::head endorsers))
          ((unless (set::in endorser (correct-addresses systate)))
           (create-endorsers-possiblep-loop cert
                                            (set::tail endorsers)
                                            systate))
          ((unless (create-endorser-possiblep
                    cert
                    (get-validator-state endorser systate)))
           nil))
       (create-endorsers-possiblep-loop cert
                                        (set::tail endorsers)
                                        systate))
     ///
     (fty::deffixequiv create-endorsers-possiblep-loop
       :args ((cert certificatep) (systate system-statep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-possiblep ((cert certificatep) (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).")
   (xdoc::p
    "If the author is correct,
     the conditions in @(tsee create-author-possiblep)
     must be satisfied.
     If the author is faulty, there are no requirements
     from the author's point of view.")
   (xdoc::p
    "The conditions in @(tsee create-endorsers-possiblep) must also hold,
     which only actually constrain correct endorsers.")
   (xdoc::p
    "Although the author and some endorsers may be faulty,
     under suitable fault tolerance conditions,
     there are enough signers to guarantee that
     the new certificate does not cause equivocation,
     i.e. does not have the same author and round as an existing certificate.
     This is proved as the non-equivocation of certificates.")
   (xdoc::p
    "Note that there are no constraints on the addresses of
     faulty signers (author or endorsers).
     Recall that our model of system states
     only explicitly includes correct validators,
     whose addresses are the ones in @(tsee correct-addresses).")
   (xdoc::p
    "If the author of the certificate is correct,
     then it can calculate the active committee at the certificate's round,
     and the certificate's signers' total stake
     is at least the quorum stake of the committee.
     This derives from the definition,
     but provides a way to obtain this fact in proofs
     without having to open @('create-possiblep')
     and some of the functions it calls."))
  (b* (((certificate cert) cert)
       ((unless (or (not (set::in cert.author (correct-addresses systate)))
                    (create-author-possiblep
                     cert
                     (get-validator-state cert.author systate))))
        nil)
       ((unless (create-endorsers-possiblep cert systate))
        nil))
    t)
  :hooks (:fix)

  ///

  (defruled author-quorum-when-create-possiblep
    (implies (and (set::in (certificate->author cert)
                           (correct-addresses systate))
                  (create-possiblep cert systate))
             (b* ((commtt (active-committee-at-round
                           (certificate->round cert)
                           (validator-state->blockchain
                            (get-validator-state (certificate->author cert)
                                                 systate)))))
               (and commtt
                    (set::subset (certificate->signers cert)
                                 (committee-members commtt))
                    (>= (committee-members-stake (certificate->signers cert)
                                                 commtt)
                        (committee-quorum-stake commtt)))))
    :enable (create-author-possiblep
             create-signer-possiblep
             certificate->signers
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-author-next ((cert certificatep) (vstate validator-statep))
  :returns (new-vstate validator-statep)
  :short "New correct author state
          resulting from a @('create') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is the certificate's author.
     See the (indirect) callers of this function.")
   (xdoc::p
    "The certificate is added to the DAG."))
  (b* ((dag (validator-state->dag vstate))
       (new-dag (set::insert (certificate-fix cert) dag)))
    (change-validator-state vstate :dag new-dag))
  :hooks (:fix)

  ///

  (defret validator-state->round-of-create-author-next
    (equal (validator-state->round new-vstate)
           (validator-state->round vstate)))

  (defret validator-state->dag-of-create-author-next
    (equal (validator-state->dag new-vstate)
           (set::insert (certificate-fix cert)
                        (validator-state->dag vstate))))
  (in-theory (disable validator-state->dag-of-create-author-next))

  (defret validator-state->buffer-of-create-author-next
    (equal (validator-state->buffer new-vstate)
           (validator-state->buffer vstate)))

  (defret validator-state->endorsed-of-create-author-next
    (equal (validator-state->endorsed new-vstate)
           (validator-state->endorsed vstate)))

  (defret validator-state->last-of-create-author-next
    (equal (validator-state->last new-vstate)
           (validator-state->last vstate))
    :hints (("Goal" :in-theory (enable nfix))))

  (defret validator-state->blockchain-of-create-author-next
    (equal (validator-state->blockchain new-vstate)
           (validator-state->blockchain vstate)))

  (defret validator-state->committed-of-create-author-next
    (equal (validator-state->committed new-vstate)
           (validator-state->committed vstate)))

  (defret validator-state->timer-of-create-author-next
    (equal (validator-state->timer new-vstate)
           (validator-state->timer vstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-endorser-next ((cert certificatep) (vstate validator-statep))
  :returns (new-vstate validator-statep)
  :short "New correct endorser state
          resulting from a @('create') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is @('endorser').
     See the (indirect) callers of this function.")
   (xdoc::p
    "The author-round pair of the certificate
     is added to the set of endorsed author-round pairs."))
  (b* (((certificate cert) cert)
       (endorsed (validator-state->endorsed vstate))
       (new-endorsed (set::insert (make-address+pos :address cert.author
                                                    :pos cert.round)
                                  endorsed)))
    (change-validator-state vstate :endorsed new-endorsed))
  :hooks (:fix)

  ///

  (defret validator-state->round-of-create-endorser-next
    (equal (validator-state->round new-vstate)
           (validator-state->round vstate)))

  (defret validator-state->dag-of-create-endorser-next
    (equal (validator-state->dag new-vstate)
           (validator-state->dag vstate)))

  (defret validator-state->buffer-of-create-endorser-next
    (equal (validator-state->buffer new-vstate)
           (validator-state->buffer vstate)))

  (defret validator-state->endorsed-of-create-endorser-next
    (equal (validator-state->endorsed new-vstate)
           (set::insert (make-address+pos
                         :address (certificate->author cert)
                         :pos (certificate->round cert))
                        (validator-state->endorsed vstate))))
  (in-theory (disable validator-state->endorsed-of-create-endorser-next))

  (defret validator-state->last-of-create-endorser-next
    (equal (validator-state->last new-vstate)
           (validator-state->last vstate))
    :hints (("Goal" :in-theory (enable nfix))))

  (defret validator-state->blockchain-of-create-endorser-next
    (equal (validator-state->blockchain new-vstate)
           (validator-state->blockchain vstate)))

  (defret validator-state->committed-of-create-endorser-next
    (equal (validator-state->committed new-vstate)
           (validator-state->committed vstate)))

  (defret validator-state->timer-of-create-endorser-next
    (equal (validator-state->timer new-vstate)
           (validator-state->timer vstate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-endorsers-next ((cert certificatep) (systate system-statep))
  :returns (new-systate system-statep)
  :short "Update, in a system state, to a certificate's endorsers' states
          resulting from a @('create') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).")
   (xdoc::p
    "We update the states of the correct endorsers.
     The faulty endorsers have no internal state."))
  (create-endorsers-next-loop cert (certificate->endorsers cert) systate)
  :hooks (:fix)

  :prepwork
  ((define create-endorsers-next-loop ((cert certificatep)
                                       (endorsers address-setp)
                                       (systate system-statep))
     :returns (new-systate system-statep)
     :parents nil
     (b* (((when (set::emptyp endorsers)) (system-state-fix systate))
          (endorser (set::head endorsers))
          ((unless (set::in endorser (correct-addresses systate)))
           (create-endorsers-next-loop cert (set::tail endorsers) systate))
          (vstate (get-validator-state endorser systate))
          (new-vstate (create-endorser-next cert vstate))
          (new-systate (update-validator-state endorser new-vstate systate)))
       (create-endorsers-next-loop cert (set::tail endorsers) new-systate))

     ///

     (fty::deffixequiv create-endorsers-next-loop
       :args ((systate system-statep) (cert certificatep)))

     (defret correct-addresses-of-create-endorsers-next-loop
       (equal (correct-addresses new-systate)
              (correct-addresses systate))
       :hints (("Goal" :induct t)))

     (defret validator-state->round-of-create-endorsers-next-loop
       (equal (validator-state->round (get-validator-state val new-systate))
              (validator-state->round (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret validator-state->dag-of-create-endorsers-next-loop
       (equal (validator-state->dag (get-validator-state val new-systate))
              (validator-state->dag (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret validator-state->buffer-of-create-endorsers-next-loop
       (equal (validator-state->buffer (get-validator-state val new-systate))
              (validator-state->buffer (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret validator-state->endorsed-of-create-endorsers-next-loop
       (equal (validator-state->endorsed (get-validator-state val new-systate))
              (if (set::in val endorsers)
                  (set::insert (make-address+pos
                                :address (certificate->author cert)
                                :pos (certificate->round cert))
                               (validator-state->endorsed
                                (get-validator-state val systate)))
                (validator-state->endorsed
                 (get-validator-state val systate))))
       :hyp (set::in val (correct-addresses systate))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable validator-state->endorsed-of-create-endorser-next
                            get-validator-state-of-update-validator-state))))
     (in-theory
      (disable validator-state->endorsed-of-create-endorsers-next-loop))

     (defret validator-state->last-of-create-endorsers-next-loop
       (equal (validator-state->last (get-validator-state val new-systate))
              (validator-state->last (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret validator-state->blockchain-of-create-endorsers-next-loop
       (equal
        (validator-state->blockchain (get-validator-state val new-systate))
        (validator-state->blockchain (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret validator-state->committed-of-create-endorsers-next-loop
       (equal (validator-state->committed (get-validator-state val new-systate))
              (validator-state->committed (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret validator-state->timer-of-create-endorsers-next-loop
       (equal (validator-state->timer (get-validator-state val new-systate))
              (validator-state->timer (get-validator-state val systate)))
       :hints
       (("Goal"
         :induct t
         :in-theory (enable get-validator-state-of-update-validator-state))))

     (defret get-network-state-of-create-endorsers-next-loop
       (equal (get-network-state new-systate)
              (get-network-state systate))
       :hints (("Goal" :induct t)))))

  ///

  (defret correct-addresses-of-create-endorsers-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate)))

  (defret validator-state->round-of-create-endorsers-next
    (equal (validator-state->round (get-validator-state val new-systate))
           (validator-state->round (get-validator-state val systate))))

  (defret validator-state->dag-of-create-endorsers-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (validator-state->dag (get-validator-state val systate))))

  (defret validator-state->buffer-of-create-endorsers-next
    (equal (validator-state->buffer (get-validator-state val new-systate))
           (validator-state->buffer (get-validator-state val systate))))

  (defret validator-state->endorsed-of-create-endorsers-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (if (set::in val (certificate->endorsers cert))
               (set::insert (make-address+pos
                             :address (certificate->author cert)
                             :pos (certificate->round cert))
                            (validator-state->endorsed
                             (get-validator-state val systate)))
             (validator-state->endorsed
              (get-validator-state val systate))))
    :hyp (set::in val (correct-addresses systate))
    :hints
    (("Goal"
      :in-theory
      (enable validator-state->endorsed-of-create-endorsers-next-loop))))
  (in-theory (disable validator-state->endorsed-of-create-endorsers-next))

  (defret validator-state->last-of-create-endorsers-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate))))

  (defret validator-state->blockchain-of-create-endorsers-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate))))

  (defret validator-state->committed-of-create-endorsers-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate))))

  (defret validator-state->timer-of-create-endorsers-next
    (equal (validator-state->timer (get-validator-state val new-systate))
           (validator-state->timer (get-validator-state val systate))))

  (defret get-network-state-of-create-endorsers-next
    (equal (get-network-state new-systate)
           (get-network-state systate))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-next ((cert certificatep) (systate system-statep))
  :guard (create-possiblep cert systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('create') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create') event;
     see @(tsee event).")
   (xdoc::p
    "If the author is correct, its state is updated
     using @(tsee create-author-next).")
   (xdoc::p
    "The states of the correct endorsers are updated
     using @(tsee create-endorsers-next);
     this only affects correct endorsers,
     since we only explicitly model the state of correct validators.")
   (xdoc::p
    "The certificate is broadcast to all the correct validators,
     except for the author if correct.
     This is realized by adding to the network
     one message for each correct validator as destination
     (except the author if correct),
     all containing the certificate.
     The deletion (via @(tsee set::delete)) of the certificate's author
     from the set of all correct validators has no effect
     if the certtificate's author is faulty, as appropriate.")
   (xdoc::p
    "It may seems strange that the messages are sent only to correct validators,
     since a validator does not know which validators are correct or faulty.
     An AleoBFT implementation would send them to all validators,
     but faulty validators behave arbitrarily regardless of
     which messages they receive.
     Thus, in our model of AleoBFT, we ignore messages sent to faulty validators
     by only adding to the network messages sent to correct validators.
     After all, recall again that our system model
     only explicitly includes correct, not faulty, validators.")
   (xdoc::p
    "It may also seem strange that the messages are sent to
     all the (correct) validators in the system,
     and not just the ones in the committee.
     An AleoBFT implementation would only send them to the committee.
     However, as explained in @(tsee system-states),
     our model of AleoBFT implicitly models syncing
     by including all possible validators in the system,
     and by having all of them update their internal states
     based on certificates generated by the active committee.
     This is way our model adds to the network messages to all validators:
     in this modeling approach, it is in fact critical that
     the certificate is broadcast not just to the committees,
     but to all the validators.")
   (xdoc::p
    "In our model, adding a message to the network implies that
     the message can always be eventually delivered,
     i.e. it is never lost.
     This matches the typical assumption, in the BFT literature,
     of eventually reliable, and authenticated, network connections.
     The authentication comes from the fact that
     the certificate in the message includes the author,
     which is also the sender.
     There is no event, in our model, to drop or modify messages in the network.
     They can only be added, and removed when delivered to validators.
     In an implementation, this kind of network behavior can be realized
     via encryption and re-transmissions on top of TCP/IP;
     the extent to which this actually realizes the network assumptions
     should be subjected to more rigorous study,
     but for now we accept this assumption as realistic,
     which is customary in the BFT literature.")
   (xdoc::p
    "If a certificate is authored by a faulty validator,
     the validator may not send the certificate to any validator,
     but in this case it is as if no certificate creation takes place:
     we do not model the internal state of faulty validators;
     we are only concerned with the effects that
     faulty validator's messages can have on correct validators.")
   (xdoc::p
    "If a faulty validator authors a certificate,
     the validator may only send it to some validators, not all of them.
     If it only sends it to faulty validators,
     then again it is as if the certificate creation never happened.
     If it sends it to at least one correct validator,
     the correct validator will be able to send it to other correct validators,
     and eventually all correct validators should have it:
     this is the underlying reliable broadcast assumption,
     which in our model is represented simply by
     the way we model the network and how messages are added and removed."))
  (b* (((certificate cert) cert)
       (systate
        (if (set::in cert.author (correct-addresses systate))
            (b* ((vstate (get-validator-state cert.author systate))
                 (new-vstate (create-author-next cert vstate)))
              (update-validator-state cert.author new-vstate systate))
          systate))
       (systate (create-endorsers-next cert systate))
       (network (get-network-state systate))
       (msgs (make-certificate-messages cert
                                        (set::delete
                                         cert.author
                                         (correct-addresses systate))))
       (new-network (set::union msgs network))
       (systate (update-network-state new-network systate)))
    systate)
  :hooks (:fix)

  ///

  (defret correct-addresses-of-create-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate)))

  (defret validator-state->round-of-create-next
    (equal (validator-state->round (get-validator-state val new-systate))
           (validator-state->round (get-validator-state val systate)))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state))))

  (defret validator-state->dag-of-create-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (if (equal val (certificate->author cert))
               (set::insert (certificate-fix cert)
                            (validator-state->dag
                             (get-validator-state val systate)))
             (validator-state->dag (get-validator-state val systate))))
    :hyp (set::in val (correct-addresses systate))
    :hints
    (("Goal" :in-theory (enable validator-state->dag-of-create-author-next))))
  (in-theory (disable validator-state->dag-of-create-next))

  (defret validator-state->buffer-of-create-next
    (equal (validator-state->buffer (get-validator-state val new-systate))
           (validator-state->buffer (get-validator-state val systate)))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state))))

  (defret validator-state->endorsed-of-create-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (if (set::in val (certificate->endorsers cert))
               (set::insert (make-address+pos
                             :address (certificate->author cert)
                             :pos (certificate->round cert))
                            (validator-state->endorsed
                             (get-validator-state val systate)))
             (validator-state->endorsed
              (get-validator-state val systate))))
    :hyp (set::in val (correct-addresses systate))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state
                         validator-state->endorsed-of-create-author-next
                         validator-state->endorsed-of-create-endorsers-next))))
  (in-theory (disable validator-state->endorsed-of-create-next))

  (defret validator-state->last-of-create-next
    (equal (validator-state->last (get-validator-state val new-systate))
           (validator-state->last (get-validator-state val systate)))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state))))

  (defret validator-state->blockchain-of-create-next
    (equal (validator-state->blockchain (get-validator-state val new-systate))
           (validator-state->blockchain (get-validator-state val systate)))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state))))

  (defret validator-state->committed-of-create-next
    (equal (validator-state->committed (get-validator-state val new-systate))
           (validator-state->committed (get-validator-state val systate)))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state))))

  (defret validator-state->timer-of-create-next
    (equal (validator-state->timer (get-validator-state val new-systate))
           (validator-state->timer (get-validator-state val systate)))
    :hints
    (("Goal"
      :in-theory (enable get-validator-state-of-update-validator-state))))

  (defret get-network-state-of-create-next
    (equal (get-network-state new-systate)
           (set::union (get-network-state systate)
                       (make-certificate-messages
                        cert (set::delete (certificate->author cert)
                                          (correct-addresses systate)))))
    :hints
    (("Goal" :in-theory (enable set::union-symmetric)))))
