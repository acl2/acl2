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

(include-book "signer-quorum")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ rounds-in-committees
  :parents (correctness)
  :short "Invariant that the authors of
          the certificates in each round of a validator's DAG
          are members of the active committee at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a consequence of the invariant that
     the signers of each accepted certificate form a quorum
     in the active committee at the certificate's round
     (see @(see signer-quorum)).
     Since the author is one of the signers,
     the author of that certificate is in the committee.
     That is the case for all the certificates at the same round.
     Thus, all the authors of the certificates at a round
     are in the committee that is active at that round.
     This holds only if there is at least one certificate at that round,
     which guarantees, by @(see accepted-certificate-committee),
     that the active committee can be calculated."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk rounds-in-committees-p ((systate system-statep))
  :guard (accepted-certificate-committee-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every correct validator
          and every round in the DAG of the validator with certificates,
          the authors of those certificates, if there is at least one,
          are members of the active committee at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "The previously proved invariant @(tsee accepted-certificate-committee-p),
     which is used as a guard here,
     guarantees that the validator can indeed calculate the committee,
     if the DAG has any certificates at that round."))
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (dag-rounds-in-committees-p
                    (validator-state->dag
                     (get-validator-state val systate))
                    (validator-state->blockchain
                     (get-validator-state val systate))
                    (all-addresses systate))))
  :guard-hints
  (("Goal"
    :in-theory
    (enable dag-committees-p-when-accepted-certificate-committee-p)))
  ///
  (fty::deffixequiv-sk rounds-in-committees-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled author-in-committee-when-validator-signer-quorum-p
  :short "If @(tsee validator-signer-quorum-p) holds,
          the certificate's author is in the committee for its round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple consequence of
     the definition of @(tsee validator-signer-quorum-p),
     which applies to all signers, and thus to the author in particular."))
  (implies (validator-signer-quorum-p cert vstate all-vals)
           (b* ((commtt (active-committee-at-round
                         (certificate->round cert)
                         (validator-state->blockchain vstate)
                         all-vals)))
             (set::in (certificate->author cert)
                      (committee-members commtt))))
  :enable (validator-signer-quorum-p
           certificate->signers))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled authors-in-committee-when-signer-quorum-p
  :short "If @(tsee signer-quorum-p) holds,
          the authors of the certificates at a round
          are in the active committees for that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove the inclusion via the pick-a-point strategy,
     so we prove a local lemma for a generic element;
     the proof of that lemma is most of the work.")
   (xdoc::p
    "The proof of the lemma makes use of
     @(tsee author-in-committee-when-validator-signer-quorum-p) above.
     The certificate is the one with the author and round of interest
     (i.e. the variables @('author') and @('round') in the theorem.
     That certificate is the expressed as
     the first one of @(tsee certificates-with-author)
     applied to @(tsee certificates-with-round);
     this would be actually equivalent to
     @(tsee certificate-with-author+round),
     but there is no need for that equivalence in this proof."))
  (implies (and (signer-quorum-p systate)
                (set::in val (correct-addresses systate)))
           (b* ((commtt (active-committee-at-round
                         round
                         (validator-state->blockchain
                          (get-validator-state val systate))
                         (all-addresses systate))))
             (set::subset (cert-set->author-set
                           (certificates-with-round
                            round
                            (validator-state->dag
                             (get-validator-state val systate))))
                          (committee-members commtt))))
  :enable set::expensive-rules
  :prep-lemmas
  ((defrule lemma
     (implies (and (signer-quorum-p systate)
                   (set::in val (correct-addresses systate)))
              (b* ((commtt (active-committee-at-round
                            round
                            (validator-state->blockchain
                             (get-validator-state val systate))
                            (all-addresses systate))))
                (implies (set::in author
                                  (cert-set->author-set
                                   (certificates-with-round
                                    round
                                    (validator-state->dag
                                     (get-validator-state val systate)))))
                         (set::in author
                                  (committee-members commtt)))))
     :enable (in-cert-set->author-set-to-nonempty-certs-with-author
              in-of-certificates-with-author
              in-of-certificates-with-round
              accepted-certificates
              signer-quorum-p-necc)
     :use ((:instance set::in-head
                      (x (certificates-with-author
                          author
                          (certificates-with-round
                           round
                           (validator-state->dag
                            (get-validator-state val systate))))))
           (:instance author-in-committee-when-validator-signer-quorum-p
                      (cert (set::head
                             (certificates-with-author
                              author
                              (certificates-with-round
                               round
                               (validator-state->dag
                                (get-validator-state val systate))))))
                      (vstate (get-validator-state val systate))
                      (all-vals (all-addresses systate))))
     :disable set::in-head)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled rounds-in-committees-p-invariant
  :short "Proof of the invariant from other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proof is easy once we have, from above,
     @(tsee authors-in-committee-when-signer-quorum-p)."))
  (implies (and (accepted-certificate-committee-p systate)
                (signer-quorum-p systate))
           (rounds-in-committees-p systate))
  :enable (rounds-in-committees-p
           dag-rounds-in-committees-p
           authors-in-committee-when-signer-quorum-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection rounds-in-committees-p-invariant-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled rounds-in-committees-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (rounds-in-committees-p (events-next events systate)))
    :disable ((:e tau-system))
    :enable (rounds-in-committees-p-invariant
             accepted-certificate-committee-p-when-reachable
             signer-quorum-p-when-reachable)))
