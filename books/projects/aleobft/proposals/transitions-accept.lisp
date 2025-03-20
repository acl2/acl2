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

(include-book "system-states")
(include-book "committees")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ transitions-accept
  :parents (transitions)
  :short "Transitions for certificate acceptance."
  :long
  (xdoc::topstring
   (xdoc::p
    "Here we define the system state changes caused by @('accept') events.")
   (xdoc::p
    "When the network contains
     a certificate message addresses to a correct validator,
     that validator can accept the certificate,
     i.e. add it to its DAG,
     provided that it already has, in its DAG,
     all the previous certificates referenced by the certificate,
     in order to keep the DAG backward-closed,
     which is an invariant, as proved elsewhere.
     Additionally, and critically,
     the validator needs to check that the signers of the certificate
     (i.e. author and endorsers)
     form a quorum in the active committee of the certificate's round.")
   (xdoc::p
    "The accepting validator does not need to perform other checks
     on the proposal contained in the certificate,
     which in our model only involves the checks on
     the authors of the previous certificates.
     This is because, as proved elsewhere,
     by checking the quorum of signaures,
     this validator may rely on at least one correct validator
     to have performed those checks.
     Note that the validator accepting a certificate
     is never the author (because the author immediately adds it to the DAG)
     and may or may not be an endorser.")
   (xdoc::p
    "Note that a certificate may be accepted by any validator in the system,
     not only validators in the committee.
     This is part of our way of modeling syncing,
     explained in @(see system-states).")
   (xdoc::p
    "In an implementation, the validator would receive the message,
     removing it from the network, prior to checking the various condition.
     If the signature quorum check fails,
     the validator would discard the message;
     in our model, the message just sits in the network forever
     (we could easily add an event to remove that message from the network).
     If not all the previous referenced certificates are present in the DAG,
     the validator would buffer the certificate,
     adding it to the DAG if and when all the previous certificates are there;
     in our model, the message sits in the network until then,
     so in a way our network models not just the actual network,
     but also some validator buffers
     (we could easily extend our model with explicit buffers,
     but it makes no real difference)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define accept-possiblep ((val addressp)
                          (cert certificatep)
                          (systate system-statep))
  :returns (yes/no booleanp)
  :short "Check if an @('accept') event is possible in a system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('val') and @('cert') parameters of this function
     are the corresponding components of the @('accept') event.")
   (xdoc::p
    "The network must contain a message containing the certificate
     and the validator as destination.")
   (xdoc::p
    "The validator must be correct;
     only correct validators have DAGs in our model.")
   (xdoc::p
    "The validator must be able to calculate
     the active committee at the round of the certificate.
     The signers of the certificate must be members of the committee,
     and must form a quorum in that committee.")
   (xdoc::p
    "The validator's DAG must already contain
     all the previous certificates referenced by the new certificate,
     unless the round is 1.")
   (xdoc::p
    "The validator's DAG must not already contain
     a certificate with the same author and round.
     Certificates created by correct validators are unique,
     and are sent at most once to each validator;
     however, faulty validators may create and send
     multiple certificates with the same proposal
     and with different signing quora
     (see @(see transitions-certify))."))
  (b* ((msg (make-message-certificate :certificate cert :destination val))
       ((unless (set::in msg (get-network-state systate))) nil)
       ((unless (set::in (address-fix val) (correct-addresses systate))) nil)
       ((validator-state vstate) (get-validator-state val systate))
       ((certificate cert) cert)
       ((proposal prop) cert.proposal)
       (commtt (active-committee-at-round prop.round vstate.blockchain))
       ((unless commtt) nil)
       (signers (certificate->signers cert))
       ((unless (set::subset signers (committee-members commtt))) nil)
       ((unless (>= (committee-members-stake signers commtt)
                    (committee-quorum-stake commtt)))
        nil)
       ((unless (set::emptyp
                 (certs-with-author+round prop.author prop.round vstate.dag)))
        nil)
       ((when (= prop.round 1))
        t)
       ((unless (set::subset prop.previous
                             (cert-set->author-set
                              (certs-with-round (1- prop.round) vstate.dag))))
        nil))
    t)
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define accept-next ((val addressp)
                     (cert certificatep)
                     (systate system-statep))
  :guard (accept-possiblep val cert systate)
  :returns (new-systate system-statep)
  :short "New system state resulting from an @('accept') event."
  :long
  (xdoc::topstring
   (xdoc::p
    "The message is removed from the network.")
   (xdoc::p
    "The certificate is added to the DAG of the validator.")
   (xdoc::p
    "The proposal of the certificate is removed from
     the set of proposals endorsed by the validator.
     This is a no-op if the validator
     has not actually endorsed the proposal."))
  (b* ((msg (make-message-certificate :certificate cert :destination val))
       (network (get-network-state systate))
       (new-network (set::delete msg network))
       (systate (update-network-state new-network systate))
       ((validator-state vstate) (get-validator-state val systate))
       (new-dag (set::insert (certificate-fix cert) vstate.dag))
       (new-endorsed (set::delete (certificate->proposal cert) vstate.endorsed))
       (new-vstate
        (change-validator-state vstate :dag new-dag :endorsed new-endorsed))
       (systate (update-validator-state val new-vstate systate)))
    systate)
  :guard-hints (("Goal" :in-theory (enable accept-possiblep)))
  :hooks (:fix)

  ///

  (defret correct-addresses-of-accept-next
    (equal (correct-addresses new-systate)
           (correct-addresses systate))
    :hyp (accept-possiblep val cert systate)
    :hints (("Goal" :in-theory (enable accept-possiblep))))

  (local (in-theory (enable get-validator-state-of-update-validator-state)))

  (defret validator-state->round-of-accept-next
    (equal (validator-state->round (get-validator-state val1 new-systate))
           (validator-state->round (get-validator-state val1 systate))))

  (defret validator-state->dag-of-accept-next
    (equal (validator-state->dag (get-validator-state val1 new-systate))
           (if (and (equal (address-fix val1) (address-fix val))
                    (set::in (address-fix val1) (correct-addresses systate)))
               (set::insert (certificate-fix cert)
                            (validator-state->dag
                             (get-validator-state val systate)))
             (validator-state->dag (get-validator-state val1 systate))))
    :hyp (accept-possiblep val cert systate)
    :hints (("Goal" :in-theory (enable accept-possiblep))))
  (in-theory (disable validator-state->dag-of-accept-next))

  (defret validator-state->proposed-of-accept-next
    (equal (validator-state->proposed (get-validator-state val1 new-systate))
           (validator-state->proposed (get-validator-state val1 systate))))

  (defret validator-state->endorsed-of-accept-next
    (equal (validator-state->endorsed (get-validator-state val1 new-systate))
           (if (equal (address-fix val1) (address-fix val))
               (set::delete (certificate->proposal cert)
                            (validator-state->endorsed
                             (get-validator-state val1 systate)))
             (validator-state->endorsed
              (get-validator-state val1 systate)))))
  (in-theory (disable validator-state->endorsed-of-accept-next))

  (defret validator-state->last-of-accept-next
    (equal (validator-state->last (get-validator-state val1 new-systate))
           (validator-state->last (get-validator-state val1 systate)))
    :hints (("Goal" :in-theory (enable nfix))))

  (defret validator-state->blockchain-of-accept-next
    (equal (validator-state->blockchain (get-validator-state val1 new-systate))
           (validator-state->blockchain (get-validator-state val1 systate))))

  (defret validator-state->committed-of-accept-next
    (equal (validator-state->committed (get-validator-state val1 new-systate))
           (validator-state->committed (get-validator-state val1 systate))))

  (defret get-network-state-of-accept-next
    (equal (get-network-state new-systate)
           (set::delete (message-certificate cert val)
                        (get-network-state systate))))
  (in-theory (disable get-network-state-of-accept-next)))
