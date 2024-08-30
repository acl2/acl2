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

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-create-certificate
  :parents (transitions)
  :short "Transitions for certificate creation."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state transitions
     caused by @('create-certificate') events.")
   (xdoc::p
    "In AleoBFT, certificates are created through an exchange of messages
     involving proposals, signatures, and certificates,
     following the Narwhal protocol, which AleoBFT is based on.
     Currently we model certificate creation as one atomic event,
     which abstracts the aforementioned message exchange process.
     Our @('create-certificate') event ``instantly'' creates a certificates,
     and broadcasts it to the other validators.
     This can be thought as modeling the final act of
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

(define create-certificate-signer-possiblep ((cert certificatep)
                                             (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of a correct signer."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is an endorser of the certificate.
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
     formalized in @(tsee create-certificate-author-possiblep);
     further conditions for the endorsers are
     formalized in @(tsee create-certificate-endorser-possiblep).")
   (xdoc::p
    "First, the signer must be able to calculate
     the active committee at the certificate's round.
     That is, its local blockchain is sufficiently far along.
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
     a @('create-certificate') event in our model,
     which involves reliable broadcast.
     This is a somewhat complex and perhaps not fully persuasive aspect
     of our current formalization of atomic certificate creation,
     but we plan to develop a more refined model
     with explcit proposals, signatures, and checks on certificates,
     which should clarify this aspect of AleoBFT.")
   (xdoc::p
    "The number of endorsers must be one less than the quorum,
     so that, with the author, there is a quorum of signatures.
     The aforementioned distinctness of the author from the endorsers
     ensures that they indeed form a quorum,
     i.e. that the author adds one to the quorum minus one.")
   (xdoc::p
    "The DAG of the signer must not already have
     a certificate with the given author and round.
     This is to prevent equivocation, i.e. the existence of
     two different certificates with the same author and round.
     Further conditions about this apply to endorsers,
     but here we are defining conditions common to author and endorsers.")
   (xdoc::p
    "The signer's DAG must include
     all the previous certificates referenced by the certificate.
     These are the certificates at the round just before the certificate's round
     whose authors are in the @('previous') component of the certificate.
     We express this condition by saying that
     the authors of all the certificates at the round before the certificate
     are a superset of the authors in the @('previous') component.
     When the signer is the author,
     this condition serves to ensure the backward closure of the DAG,
     i.e. that if the DAG includes a certificate,
     it also includes all its predecessors.
     When the signer is an endorser,
     this condition corresponds to the fact that,
     before endorsing a certificate from another validator,
     a validator checks it against the predecessors
     (something not explicit in our model),
     and therefore the validator must have those predecessors in the DAG.
     If the certificate's round is 1,
     there is no previous round, and thus no previous certificates,
     and thus no requirements on they being in the DAG.")
   (xdoc::p
    "The referenced certificate in the previous round must form a quorum,
     unless the certificate's round is 1,
     in which case there must be no references to previous certificates.
     However, note that the active committee of the previous round
     may differ from the one of the certificate's round.
     Since we already checked that the active committee of the certificate round
     is known to the signer whose conditions we are checking,
     it follows that the active committee at the previous round is also known,
     as proved in @(tsee active-committee-at-round)."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       (commtt (active-committee-at-round cert.round vstate.blockchain))
       ((unless commtt) nil)
       ((when (set::in cert.author cert.endorsers)) nil)
       ((unless (committee-memberp cert.author commtt)) nil)
       ((unless (committee-membersp cert.endorsers commtt)) nil)
       ((unless (= (set::cardinality cert.endorsers)
                   (1- (committee-quorum commtt))))
        nil)
       ((when (get-certificate-with-author+round
               cert.author cert.round vstate.dag))
        nil)
       ((unless (or (= cert.round 1)
                    (set::subset cert.previous
                                 (certificate-set->author-set
                                  (get-certificates-with-round (1- cert.round)
                                                               vstate.dag)))))
        nil)
       ((unless (= (set::cardinality cert.previous)
                   (if (= cert.round 1)
                       0
                     (b* ((prev-commtt
                           (active-committee-at-round (1- cert.round)
                                                      vstate.blockchain)))
                       (committee-quorum prev-commtt)))))
        nil))
    t)
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       active-committee-at-earlier-round-when-at-later-round)))
  :hooks (:fix)

  ///

  (defrule active-committee-at-round-when-create-certificate-signer-possiblep
    (implies (create-certificate-signer-possiblep cert vstate)
             (active-committee-at-round (certificate->round cert)
                                        (validator-state->blockchain vstate)))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-author-possiblep ((cert certificatep)
                                             (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of a correct author."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is the certificate's author.
     See the (indirect) callers of this function.")
   (xdoc::p
    "In addition to the conditions
     formalized in @(tsee create-certificate-signer-possiblep),
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
     but @(tsee create-certificate-signer-possiblep)
     already checks that the certificate author is in the committee.
     The other conditions in @(tsee create-certificate-signer-possiblep)
     are naturally checked by the certificate's author,
     who is in charge of creating the certificate."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       ((unless (create-certificate-signer-possiblep cert vstate))
        nil)
       ((unless (= cert.round vstate.round)) nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-endorser-possiblep ((cert certificatep)
                                               (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of a correct endorser."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).
     The input @('vstate') is the state of
     the validator whose address is an endorser of the certificate.
     See the (indirect) callers of this function.")
   (xdoc::p
    "In addition to the conditions
     formalized in @(tsee create-certificate-signer-possiblep),
     a correct validator endorses a certificate
     if additional conditions are satisfied.
     This function puts these additional conditions
     together with the conditions of that function.")
   (xdoc::p
    "While @(tsee create-certificate-signer-possiblep) checks that
     the DAG has no certificate already with the same author and round,
     which is sufficient for the author to check,
     an endorser must check more than that:
     the buffer of the endorser
     must not contain a certificate with the same author and round;
     and the set of endorsed author-round pairs
     does not already contain the author-round pair of the certificate.
     The presence of a pair in this set indicates that the validators
     has already endorsed a certificate with that author and round,
     but has not yet received the actual certificate from the network.")
   (xdoc::p
    "Together with the check that the DAG does not have a certificate
     with the same author and round as this new certificate,
     we are checking that the endorser has not any trace, anywhere,
     of the author-round pair of the new certificate.
     This serves to ensure the non-equivocation of certificates.")
   (xdoc::p
    "For the certificate author, in @(tsee create-certificate-author-possiblep),
     it is not necessary to check the buffer and author-round pairs:
     as already proved for AleoBFT with static committees,
     and as we plan to prove for AleoBFT with dynamic committees as well,
     a validator never has a certificate authored by itself in the buffer,
     or an author-round pair whose author component is the validator's address.
     So it suffices to check the DAG for the author."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       ((unless (create-certificate-signer-possiblep cert vstate))
        nil)
       ((when (get-certificate-with-author+round
               cert.author cert.round vstate.buffer))
        nil)
       ((when (set::in (make-address+pos :address cert.author :pos cert.round)
                       vstate.endorsed))
        nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-endorsers-possiblep ((cert certificatep)
                                                (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible,
          from the point of view of all the certificate's endorsers."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "An endorser may be correct or faulty.
     If it is correct, it must satisfy the conditions
     formalized in @(tsee create-certificate-endorser-possiblep).
     If it is faulty, it is not bound by any condition.")
   (xdoc::p
    "Note that, if there are (as normal) multiple correct endorsers,
     the conditions involving committees as viewed by the endorsers
     imply at least some agreement among the blockchains of the validators,
     enough to make consistent checks involving the committee.
     But as we plan to prove, it is a system invariant that
     different validators agree on the committees they can both calculate,
     because of the invariant that blockchains never fork.
     Thus, in each state, which satisfies the invariant,
     starting with an initial state,
     the conditions on the possibility of a @('create-certificate') event
     do not impose any more agreement requirements
     than already implied by the invariants.
     As already observed in @(tsee create-certificate-signer-possiblep),
     all of this can be made even more clear and persuasive
     in a planned more detailed model of AleoBFT
     that includes explicit proposal and signature exchanges."))
  (create-certificate-endorsers-possiblep-loop cert
                                               (certificate->endorsers cert)
                                               systate)
  :hooks (:fix)

  :prepwork
  ((define create-certificate-endorsers-possiblep-loop ((cert certificatep)
                                                        (endorsers address-setp)
                                                        (systate system-statep))
     :returns (yes/no booleanp)
     :parents nil
     (b* (((when (set::emptyp endorsers)) t)
          (endorser (set::head endorsers))
          ((unless (set::in endorser (correct-addresses systate)))
           (create-certificate-endorsers-possiblep-loop cert
                                                        (set::tail endorsers)
                                                        systate))
          ((unless (create-certificate-endorser-possiblep
                    cert
                    (get-validator-state endorser systate)))
           nil))
       (create-certificate-endorsers-possiblep-loop cert
                                                    (set::tail endorsers)
                                                    systate))
     ///
     (fty::deffixequiv create-certificate-endorsers-possiblep-loop
       :args ((cert certificatep) (systate system-statep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-possiblep ((cert certificatep)
                                      (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if a certificate creation event is possible."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "Author and endorsers must be in the system.
     Recall that the system includes all possible validators
     in all possible committees.
     More specific checks about author and endorsers being in the committee
     are formalized in @(tsee create-certificate-signer-possiblep).")
   (xdoc::p
    "If the author is correct,
     the conditions in @(tsee create-certificate-author-possiblep)
     must be satisfied.
     If the author is faulty, there are no requirements
     from the author's point of view.")
   (xdoc::p
    "The conditions in @(tsee create-certificate-endorsers-possiblep)
     must also hold, which may concern correct and faulty endorsers.")
   (xdoc::p
    "Although the author and some endorsers may be faulty,
     under suitable fault tolerance conditions,
     there are enough signers to guarantee that
     the new certificate does not cause equivocation,
     i.e. does not have the same author and round as an existing certificate.
     This has been proved for AleoBFT with static committees,
     and we are working on proving it for dynamic committees.
     Here the fault tolerance conditions has to be stated for each committee."))
  (b* (((certificate cert) cert)
       ((unless (set::in cert.author (all-addresses systate))) nil)
       ((unless (set::subset cert.endorsers (all-addresses systate))) nil)
       ((unless (or (not (set::in cert.author (correct-addresses systate)))
                    (create-certificate-author-possiblep
                     cert
                     (get-validator-state cert.author systate))))
        nil)
       ((unless (create-certificate-endorsers-possiblep cert systate))
        nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-author-next ((cert certificatep)
                                        (vstate validator-statep))
  :returns (new-vstate validator-statep)
  :short "New correct author state
          resulting from a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
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

  (defret validator-state->dag-of-create-certificate-author-next
    (equal (validator-state->dag new-vstate)
           (set::insert (certificate-fix cert)
                        (validator-state->dag vstate))))

  (defret validator-state->buffer-of-create-certificate-author-next
    (equal (validator-state->buffer new-vstate)
           (validator-state->buffer vstate)))

  (defret validator-state->endorsed-of-create-certificate-author-next
    (equal (validator-state->endorsed new-vstate)
           (validator-state->endorsed vstate)))

  (in-theory
   (disable
    validator-state->dag-of-create-certificate-author-next
    validator-state->buffer-of-create-certificate-author-next
    validator-state->endorsed-of-create-certificate-author-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-endorser-next ((cert certificatep)
                                          (vstate validator-statep))
  :returns (new-vstate validator-statep)
  :short "New correct endorser state
          resulting from a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
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

  (defret validator-state->dag-of-create-certificate-endorser-next
    (equal (validator-state->dag new-vstate)
           (validator-state->dag vstate)))

  (defret validator-state->buffer-of-create-certificate-endorser-next
    (equal (validator-state->buffer new-vstate)
           (validator-state->buffer vstate)))

  (defret validator-state->endorsed-of-create-certificate-endorser-next
    (equal (validator-state->endorsed new-vstate)
           (set::insert (make-address+pos
                         :address (certificate->author cert)
                         :pos (certificate->round cert))
                        (validator-state->endorsed vstate))))

  (in-theory
   (disable
    validator-state->dag-of-create-certificate-endorser-next
    validator-state->buffer-of-create-certificate-endorser-next
    validator-state->endorsed-of-create-certificate-endorser-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-endorsers-next ((cert certificatep)
                                           (systate system-statep))
  :returns (new-systate system-statep)
  :short "Update, in a system state, to a certificate's endorsers' states
          resulting from a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "We update the states of the correct endorsers.
     The faulty endorsers have no internal state."))
  (create-certificate-endorsers-next-loop cert
                                          (certificate->endorsers cert)
                                          systate)
  :hooks (:fix)

  :prepwork
  ((define create-certificate-endorsers-next-loop ((cert certificatep)
                                                   (endorsers address-setp)
                                                   (systate system-statep))
     :returns (new-systate system-statep)
     :parents nil
     (b* (((when (set::emptyp endorsers)) (system-state-fix systate))
          (endorser (set::head endorsers))
          ((unless (set::in endorser (correct-addresses systate)))
           (create-certificate-endorsers-next-loop cert
                                                   (set::tail endorsers)
                                                   systate))
          (vstate (get-validator-state endorser systate))
          (new-vstate (create-certificate-endorser-next cert vstate))
          (new-systate (update-validator-state endorser new-vstate systate)))
       (create-certificate-endorsers-next-loop cert
                                               (set::tail endorsers)
                                               new-systate))

     ///

     (fty::deffixequiv create-certificate-endorsers-next-loop
       :args ((systate system-statep) (cert certificatep)))

     (defret all-addresses-of-create-certificate-endorsers-next-loop
       (equal (all-addresses new-systate)
              (all-addresses systate))
       :hints (("Goal" :induct t)))

     (defret correct-addresses-of-create-certificate-endorsers-next-loop
       (equal (correct-addresses new-systate)
              (correct-addresses systate))
       :hints (("Goal" :induct t)))

     (defret faulty-addresses-of-create-certificate-endorsers-next-loop
       (equal (faulty-addresses new-systate)
              (faulty-addresses systate))
       :hints (("Goal" :induct t)))

     (defret validator-state->dag-of-create-certificate-endorsers-next-loop
       (equal (validator-state->dag (get-validator-state val new-systate))
              (validator-state->dag (get-validator-state val systate)))
       :hyp (set::in val (correct-addresses systate))
       :hints
       (("Goal"
         :induct t
         :in-theory
         (enable
          validator-state->dag-of-create-certificate-endorser-next
          get-validator-state-of-update-validator-state))))

     (defret validator-state->buffer-of-create-certificate-endorsers-next-loop
       (equal (validator-state->buffer (get-validator-state val new-systate))
              (validator-state->buffer (get-validator-state val systate)))
       :hyp (set::in val (correct-addresses systate))
       :hints
       (("Goal"
         :induct t
         :in-theory
         (enable
          validator-state->buffer-of-create-certificate-endorser-next
          get-validator-state-of-update-validator-state))))

     (defret validator-state->endorsed-of-create-certificate-endorsers-next-loop
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
         :in-theory
         (enable validator-state->endorsed-of-create-certificate-endorser-next
                 get-validator-state-of-update-validator-state))))

     (defret get-network-state-of-create-certificate-endorsers-next-loop
       (equal (get-network-state new-systate)
              (get-network-state systate))
       :hints (("Goal" :induct t)))))

  ///

  (defret all-addresses-of-create-certificate-endorsers-next
    (equal (all-addresses new-systate)
           (all-addresses systate)))

  (defret correct-addresses-of-create-certificate-endorsers-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate)))

  (defret faulty-addresses-of-create-certificate-endorsers-next
    (equal (faulty-addresses new-systate)
           (faulty-addresses systate)))

  (defret validator-state->dag-of-create-certificate-endorsers-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (validator-state->dag (get-validator-state val systate)))
    :hyp (set::in val (correct-addresses systate)))

  (defret validator-state->buffer-of-create-certificate-endorsers-next
    (equal (validator-state->buffer (get-validator-state val new-systate))
           (validator-state->buffer (get-validator-state val systate)))
    :hyp (set::in val (correct-addresses systate)))

  (defret validator-state->endorsed-of-create-certificate-endorsers-next
    (equal (validator-state->endorsed (get-validator-state val new-systate))
           (if (set::in val (certificate->endorsers cert))
               (set::insert (make-address+pos
                             :address (certificate->author cert)
                             :pos (certificate->round cert))
                            (validator-state->endorsed
                             (get-validator-state val systate)))
             (validator-state->endorsed
              (get-validator-state val systate))))
    :hyp (set::in val (correct-addresses systate)))

  (defret get-network-state-of-create-certificate-endorsers-next
    (equal (get-network-state new-systate)
           (get-network-state systate)))

  (in-theory
   (disable
    validator-state->dag-of-create-certificate-endorsers-next-loop
    validator-state->buffer-of-create-certificate-endorsers-next-loop
    validator-state->endorsed-of-create-certificate-endorsers-next-loop
    get-network-state-of-create-certificate-endorsers-next-loop
    validator-state->dag-of-create-certificate-endorsers-next
    validator-state->buffer-of-create-certificate-endorsers-next
    validator-state->endorsed-of-create-certificate-endorsers-next
    get-network-state-of-create-certificate-endorsers-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-next ((cert certificatep)
                                 (systate system-statep))
  :guard (create-certificate-possiblep cert systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from a @('create-certificate') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input @('cert') of this function is
     the certificate in the @('create-certificate') event;
     see @(tsee event).")
   (xdoc::p
    "If the author is correct, its state is updated
     using @(tsee create-certificate-author-next).")
   (xdoc::p
    "The states of the correct endorsers are updated
     using @(tsee create-certificate-endorsers-next).")
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
     We could easily change our model to add to the network
     messages to all correct validators,
     but since faulty validators have no internal state in our model,
     messages to faulty validators would have no use and purpose.")
   (xdoc::p
    "It may also seem strange that the messages are sent to
     all the validators in the system, and not just the ones in the committee.
     An AleoBFT implementation would only send them to the committee.
     However, as explained in @(tsee system-states),
     our model of AleoBFT implicitly models syncing
     by including all possible validators in the system,
     and by having all of them update their internal states
     based on certificates generated by the active committee.
     This is way our model adds to the network messages to all validators.")
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
     They can only be added, and removed when delivered.
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
                 (new-vstate (create-certificate-author-next cert vstate)))
              (update-validator-state cert.author new-vstate systate))
          systate))
       (systate (create-certificate-endorsers-next cert systate))
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

  (defret all-addresses-of-create-certificate-next
    (equal (all-addresses new-systate)
           (all-addresses systate)))

  (defret correct-addresses-of-create-certificate-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate)))

  (defret faulty-addresses-of-create-certificate-next
    (equal (faulty-addresses new-systate)
           (faulty-addresses systate)))

  (defret validator-state->dag-of-create-certificate-next
    (equal (validator-state->dag (get-validator-state val new-systate))
           (if (equal val (certificate->author cert))
               (set::insert (certificate-fix cert)
                            (validator-state->dag
                             (get-validator-state val systate)))
             (validator-state->dag (get-validator-state val systate))))
    :hyp (set::in val (correct-addresses systate))
    :hints
    (("Goal"
      :in-theory
      (enable
       validator-state->dag-of-create-certificate-author-next
       validator-state->dag-of-create-certificate-endorsers-next))))

  (defret validator-state->buffer-of-create-certificate-next
    (equal (validator-state->buffer (get-validator-state val new-systate))
           (validator-state->buffer (get-validator-state val systate)))
    :hyp (set::in val (correct-addresses systate))
    :hints
    (("Goal"
      :in-theory
      (enable
       validator-state->buffer-of-create-certificate-author-next
       validator-state->buffer-of-create-certificate-endorsers-next
       get-validator-state-of-update-validator-state))))

  (defret validator-state->endorsed-of-create-certificate-next
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
      (enable
       get-validator-state-of-update-validator-state
       validator-state->endorsed-of-create-certificate-author-next
       validator-state->endorsed-of-create-certificate-endorsers-next))))

  (defret get-network-state-of-create-certificate-next
    (equal (get-network-state new-systate)
           (set::union (get-network-state systate)
                       (make-certificate-messages
                        cert (set::delete (certificate->author cert)
                                          (correct-addresses systate)))))
    :hints
    (("Goal"
      :in-theory (enable get-network-state-of-create-certificate-endorsers-next
                         set::union-symmetric))))

  (in-theory (disable validator-state->dag-of-create-certificate-next
                      validator-state->buffer-of-create-certificate-next
                      validator-state->endorsed-of-create-certificate-next
                      get-network-state-of-create-certificate-next)))
