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
     the exchange of proposals, signatures, and certificates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-signer-possiblep ((signer addressp)
                                             (vstate validator-statep)
                                             (cert certificatep))
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
     the validator whose address is @('signer').
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
    "A condition is that the signer is in
     the active committee for the certificate's round.
     A sub-condition of this is that the signer can calculate
     the active committee at that round,
     i.e. that its local blockchain is sufficiently far along.
     The reason for this condition is that
     only validators in the active committee
     are in charge for the round of the certificate.")
   (xdoc::p
    "Another condition is that the DAG of the signer
     does not already have a certificate with the given author and round.
     This is to prevent equivocation, i.e. the existence of
     two different certificates with the same author and round.")
   (xdoc::p
    "The remaining conditions concern the presence and number of
     the previous certificates referenced by the certificate.
     If the round of the certificate is 1, there is no previous round,
     and there are no previous certificates, so there are no further conditions.
     The following conditions apply only if the certificate round is not 1.")
   (xdoc::p
    "The condition about the presence of the previous certificates
     is that the signer's DAG must include
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
     and therefore the validator must have those predecessors in the DAG.")
   (xdoc::p
    "The condition about the number of the previous certificates
     is that they must form a quorum.
     However, note that the active committee of the previous round
     may differ from the one of the certificate's round.
     Since we already checked that the active committee of the certificate round
     is known to the signer whose conditions we are checking,
     it follows that the active committee at the previous round is also known,
     as proved in @(tsee active-committee-at-round).
     Since the author of a certificate must be
     in the active committee of the certificate's round,
     as checked by this very ACL2 function,
     the authors of certificates in the previous round
     must be in the active committee for the previous round,
     and thus the quorum must be calculated on that committee."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       (commtt (active-committee-at-round cert.round vstate.blockchain))
       ((unless commtt) nil)
       ((unless (committee-memberp signer commtt)) nil)
       ((when (get-certificate-with-author+round
               cert.author cert.round vstate.dag))
        nil)
       ((when (= cert.round 1)) t)
       ((unless (set::subset cert.previous
                             (certificate-set->author-set
                              (get-certificates-with-round (1- cert.round)
                                                           vstate.dag))))
        nil)
       (prev-commtt
        (active-committee-at-round (1- cert.round) vstate.blockchain))
       ((unless (= (set::cardinality cert.previous)
                   (committee-quorum prev-commtt)))
        nil))
    t)
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       active-committee-at-earlier-round-when-at-later-round)))
  :hooks (:fix)

  ///

  (defrule active-committee-at-round-when-create-certificate-signer-possiblep
    (implies (create-certificate-signer-possiblep signer vstate cert)
             (active-committee-at-round (certificate->round cert)
                                        (validator-state->blockchain vstate)))
    :rule-classes :forward-chaining))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-author-possiblep ((vstate validator-statep)
                                             (cert certificatep))
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
    "An additional condition is that the round of the certificate
     is the current round of the validator.
     A correct validator only creates (at most) one certificate per round.")
   (xdoc::p
    "Another condition is that the author is distinct from the endorsers.
     When proposals and signatures are explicitly exchanged,
     a correct certificate author would not
     send the proposal to itself
     and receive the signature from itself.
     Here we model this exchange at an abstract level,
     so we need to check this condition in our model.")
   (xdoc::p
    "Another additional condition is that
     the number of endorsers must be one less than the quorum,
     so that, with the author, there is a quorum of signatures.
     Note that the distinctness of the author from the endorsers
     ensures that indeed they form a quorum,
     i.e. that the author adds one to the quorum minus one.")
   (xdoc::p
    "Note that the inclusion of the check that
     @(tsee create-certificate-signer-possiblep) holds
     guarantees that the committee at the round is known,
     so there is no need to re-check that here."))
  (b* (((certificate cert) cert)
       ((validator-state vstate) vstate)
       ((unless (create-certificate-signer-possiblep cert.author vstate cert))
        nil)
       ((unless (= cert.round vstate.round)) nil)
       ((when (set::in cert.author cert.endorsers)) nil)
       (commtt (active-committee-at-round cert.round vstate.blockchain))
       ((unless (= (set::cardinality cert.endorsers)
                   (1- (committee-quorum commtt))))
        nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-endorser-possiblep ((endorser addressp)
                                               (vstate validator-statep)
                                               (cert certificatep))
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
     the validator whose address is @('endorser').
     See the (indirect) callers of this function.")
   (xdoc::p
    "In addition to the conditions
     formalized in @(tsee create-certificate-signer-possiblep),
     a correct validator endorses a certificate
     if additional conditions are satisfied.
     This function puts these additional conditions
     together with the conditions of that function.")
   (xdoc::p
    "An additional condition is that the buffer of the endorser
     must not contain a certificate with the same author and round.
     This serves to ensure the non-equivocation of certificates.")
   (xdoc::p
    "Another additional condition is that
     the set of endorsed author-round pairs
     does not already contain the author-round pair of the certificate.
     This also serves to ensure the non-equivocation of certificates.
     The presence of a pair in this set indicates that the validators
     has already endorsed a certificate with that author and round,
     but has not yet received the actual certificate from the network.")
   (xdoc::p
    "Together with the check that the DAG does not have a certificate
     with the same author and round as this new certificate,
     which is performed in @(tsee create-certificate-signer-possiblep),
     we are checking that the endorser has not any trace, anywhere,
     of the author-round pair of the new certificate.")
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
       ((unless (create-certificate-signer-possiblep endorser vstate cert))
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

(define create-certificate-endorsers-possiblep ((systate system-statep)
                                                (cert certificatep))
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
     If it is faulty, it is not bound by any condition."))
  (create-certificate-endorsers-possiblep-loop (certificate->endorsers cert)
                                               systate
                                               cert)
  :hooks (:fix)

  :prepwork
  ((define create-certificate-endorsers-possiblep-loop ((endorsers address-setp)
                                                        (systate system-statep)
                                                        (cert certificatep))
     :returns (yes/no booleanp)
     :parents nil
     (b* (((when (set::emptyp endorsers)) t)
          (endorser (set::head endorsers))
          ((unless (set::in endorser (correct-addresses systate)))
           (create-certificate-endorsers-possiblep-loop (set::tail endorsers)
                                                        systate
                                                        cert))
          ((unless (create-certificate-endorser-possiblep
                    endorser
                    (get-validator-state endorser systate)
                    cert))
           nil))
       (create-certificate-endorsers-possiblep-loop (set::tail endorsers)
                                                    systate
                                                    cert))
     ///
     (fty::deffixequiv create-certificate-endorsers-possiblep-loop
       :args ((systate system-statep) (cert certificatep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-certificate-possiblep ((systate system-statep)
                                      (cert certificatep))
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
                     (get-validator-state cert.author systate)
                     cert)))
        nil)
       ((unless (create-certificate-endorsers-possiblep systate cert))
        nil))
    t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: define create-certificate-next
