; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "system-states")
(include-book "operations-certificate-retrieval")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-author-round-pairs
  :parents (operations)
  :short "Operatiosn for handling author-round pairs."
  :long
  (xdoc::topstring
   (xdoc::p
    "As defined in @(tsee validator-state),
     each (correct) validator has a set of author-round pairs,
     used to track which certificates it has endorsed (i.e. signed)
     but not yet received from the network.
     Besides this set, the author-round pairs in full certificates,
     either in the DAG or in the buffer,
     are also used along with the ones in the set for certain purposes.")
   (xdoc::p
    "We introduce operations to check whether
     validators do not have a certain author-round pair
     (in the set or in the DAG or in the buffer),
     which is a critical condition for (correct) validators
     to endorse a certificate with a certain author and round.
     We also introduce operations to add pairs to the set,
     used when the condition above is fulfilled
     and validators endorse a certificate."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signer-does-not-have-author+round-p ((signer addressp)
                                             (author addressp)
                                             (round posp)
                                             (systate system-statep))
  :guard (set::in signer (all-addresses systate))
  :returns (yes/no booleanp)
  :short "Check whether a validator who signed a certificate
          does not have, and has not signed, already a certificate
          with the same author and round number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to define @(tsee signers-do-not-have-author+round-p):
     see that function's documentation for motivation.
     This function performs the check on a single validator.
     If the validator is faulty, the check passes:
     there is no requirement on faulty validators from this standpoint.
     If the validator is correct,
     we check that there is no record of the author and round
     in the DAG, buffer, or set of endorsed pairs."))
  (b* ((vstate (get-validator-state signer systate)))
    (or (not vstate)
        (b* ((dag (validator-state->dag vstate))
             (buffer (validator-state->buffer vstate))
             (endorsed (validator-state->endorsed vstate)))
          (and (not (certificate-with-author+round author round dag))
               (not (certificate-with-author+round author round buffer))
               (not (set::in (make-address+pos :address author :pos round)
                             endorsed))))))

  ///

  (fty::deffixequiv signer-does-not-have-author+round-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signers-do-not-have-author+round-p ((signers address-setp)
                                            (author addressp)
                                            (round posp)
                                            (systate system-statep))
  :guard (set::subset signers (all-addresses systate))
  :returns (yes/no booleanp)
  :short "Check whether all the correct validators who signed a certificate
          do not have, and have not signed, already a certificate
          with the same author and round number."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee create-certificate-possiblep)
     to express one of the conditions under which the event is possible.
     The condition is that
     every validator that signed a certificate,
     if it is a correct validator,
     does not have, in its DAG or buffer,
     already a certificate with the same author and round number;
     and furthermore,
     it does not have a record of signing any certificate
     with that author and round number.
     The latter additional condition,
     which is checked against the @('endorsed') component
     of the state of the correct validator,
     is needed because, after signing a proposal,
     the certificate for that proposal may take time to reach the signer.
     If, in the meanwhile, a faulty validator sends a different proposal
     with the same round number (and obviously same author),
     and the signer has not received the certificate yet,
     the signer may erroneously think that the proposal is valid and sign it.
     This is why we need the @('endorsed') state component.")
   (xdoc::p
    "The first input to this ACL2 function consists of
     the signers (author and endorsers) of the certificate;
     see call in @(tsee create-certificate-possiblep).
     The second and third inputs are
     the author and round number of the certificate.")
   (xdoc::p
    "We go through each signer,
     and call the function to check an individual signer.
     The rationale is that, in AleoBFT,
     a correct validator will not sign a certificate
     if it duplicates another certificate's author and round number,
     in order to prevent equivocation."))
  (or (set::emptyp signers)
      (and (signer-does-not-have-author+round-p (set::head signers)
                                                author round systate)
           (signers-do-not-have-author+round-p (set::tail signers)
                                               author round systate)))
  :guard-hints (("Goal" :in-theory (enable* set::expensive-rules)))

  ///

  (fty::deffixequiv signers-do-not-have-author+round-p
    :args ((systate system-statep)))

  (defruled signers-do-not-have-author+round-p-element
    (implies (and (signers-do-not-have-author+round-p
                   signers author round systate)
                  (set::in signer signers))
             (signer-does-not-have-author+round-p signer author round systate))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-endorsed-val ((author addressp)
                          (round posp)
                          (vstate validator-statep))
  :returns (new-vstate validator-statep)
  :short "Add an author-pair to the set of endorsed pairs
          in the state of a correct validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in @(tsee add-endorsed).
     See the documentation of that function."))
  (b* ((endorsed (validator-state->endorsed vstate))
       (new-endorsed (set::insert (make-address+pos
                                   :address author
                                   :pos round)
                                  endorsed)))
    (change-validator-state vstate :endorsed new-endorsed)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define add-endorsed ((endorsers address-setp)
                      (author addressp)
                      (round posp)
                      (systate system-statep))
  :guard (set::subset endorsers (all-addresses systate))
  :returns (new-systate system-statep)
  :short "Add an author-round pair to the set of endorsed pairs of
          all the correct validators in a given set of endorsers."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created by a (correct or faulty) validator,
     it must have been signed by the validators
     whose addresses are in the @('endorsers') component of the certificate.
     As discussed in @(tsee signers-do-not-have-author+round-p),
     this signing must leave a record in the state of correct validators,
     in the form of an author-round pair added to the set of such pairs.
     This addition is described by this ACL2 function:
     we go through all the endorsers, and if correct,
     we add the pair to their set."))
  (b* (((when (set::emptyp endorsers)) (system-state-fix systate))
       (endorser (set::head endorsers))
       (vstate (get-validator-state endorser systate))
       (systate
        (if vstate
            (b* ((new-vstate
                  (add-endorsed-val author round vstate)))
              (update-validator-state endorser new-vstate systate))
          systate)))
    (add-endorsed (set::tail endorsers) author round systate))
  :guard-hints
  (("Goal"
    :in-theory
    (enable* in-correct-validator-addresess-when-get-validator-state
             set::expensive-rules)))

  ///

  (fty::deffixequiv add-endorsed
    :args ((systate system-statep)))

  (defret get-network-state-of-add-endorsed
    (equal (get-network-state new-systate)
           (get-network-state systate))
    :hints (("Goal" :induct t)))

  (defret all-addresses-of-add-endorsed
    (equal (all-addresses new-systate)
           (all-addresses systate))
    :hyp (set::subset endorsers (all-addresses systate))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::expensive-rules))))

  (defret correct-addresses-of-add-endorsed
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (set::subset endorsers (all-addresses systate))
    :hints
    (("Goal"
      :induct t
      :in-theory
      (enable* in-correct-validator-addresess-when-get-validator-state
               set::expensive-rules))))

  (defruled validator-state->round-of-add-endorsed
    (equal (validator-state->round
            (get-validator-state
             val
             (add-endorsed endorsers author round systate)))
           (validator-state->round (get-validator-state val systate)))
    :induct t
    :enable (add-endorsed-val
             in-correct-validator-addresess-when-get-validator-state
             get-validator-state-of-update-validator-state))

  (defruled validator-state->dag-of-add-endorsed
    (equal (validator-state->dag
            (get-validator-state
             val
             (add-endorsed endorsers author round systate)))
           (validator-state->dag (get-validator-state val systate)))
    :induct t
    :enable (in-correct-validator-addresess-when-get-validator-state
             add-endorsed-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->buffer-of-add-endorsed
    (equal (validator-state->buffer
            (get-validator-state
             val
             (add-endorsed endorsers author round systate)))
           (validator-state->buffer (get-validator-state val systate)))
    :induct t
    :enable (in-correct-validator-addresess-when-get-validator-state
             add-endorsed-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->endorsed-of-add-endorsed
    (equal (validator-state->endorsed
            (get-validator-state
             val
             (add-endorsed endorsers author round systate)))
           (if (and (set::in val endorsers)
                    (set::in val (correct-addresses systate)))
               (set::insert (address+pos author round)
                            (validator-state->endorsed
                             (get-validator-state val systate)))
             (validator-state->endorsed
              (get-validator-state val systate))))
    :induct t
    :enable (in-correct-validator-addresess-when-get-validator-state
             add-endorsed-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->last-of-add-endorsed
    (implies (set::in val (correct-addresses systate))
             (equal (validator-state->last
                     (get-validator-state val
                                          (add-endorsed
                                           endorsers author round systate)))
                    (validator-state->last
                     (get-validator-state val systate))))
    :induct t
    :enable (in-correct-validator-addresess-when-get-validator-state
             add-endorsed-val
             get-validator-state-of-update-validator-state
             nfix))

  (defruled validator-state->blockchain-of-add-endorsed
    (implies (set::in val (correct-addresses systate))
             (equal (validator-state->blockchain
                     (get-validator-state val
                                          (add-endorsed
                                           endorsers author round systate)))
                    (validator-state->blockchain
                     (get-validator-state val systate))))
    :induct t
    :enable (in-correct-validator-addresess-when-get-validator-state
             add-endorsed-val
             get-validator-state-of-update-validator-state))

  (defruled validator-state->committed-of-add-endorsed
    (implies (set::in val (correct-addresses systate))
             (equal (validator-state->committed
                     (get-validator-state val
                                          (add-endorsed
                                           endorsers author round systate)))
                    (validator-state->committed
                     (get-validator-state val systate))))
    :induct t
    :enable (in-correct-validator-addresess-when-get-validator-state
             add-endorsed-val
             get-validator-state-of-update-validator-state)))
