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

(include-book "owned-certificates")
(include-book "ordered-even-blocks")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signers-qourum-in-committee
  :parents (correctness)
  :short "Invariant that the signers of each certificate
          form a quorum in the active committee for the certificate's round."
  :long
  (xdoc::topstring
   (xdoc::p
    "The formulation of the invariant as stated above needs clarification,
     because the notion of active committee is not a universal one,
     but rather it is calculated by individual validators.
     So by that we mean the active committee calculated by
     any of the correct signers of the certificate.
     Our model of certificate creation requires signers
     to be able to calculate that committee when the certificate is created:
     see @(tsee create-certificate-possiblep) and the functions it calls.")
   (xdoc::p
    "Initially there are no certificates, so the invariant holds.
     The only kind of event that introduces a new certificate
     is @('create-certificate'),
     but @(tsee create-certificate-possiblep)
     requires each correct signer to be in the committee they calculate,
     and all the signers (correct or faulty) to be in that committee,
     so the invariant is preserved."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-signers-quorum-in-committee-p ((cert certificatep)
                                                 (vstate validator-statep)
                                                 (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if a validator (represented by its state)
          can calculate the active committee for a certificate,
          if the committee contains all the signers,
          and if the signers form a quorum in the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee signers-quorum-in-committee-p)
     to define our invariant.
     The validator whose state is @('vstate') is a correct signer.")
   (xdoc::p
    "We prove that if two validator states have the same blockchain,
     this predicate returns the same value on them,
     for the same certificate and set of all validator addresses.
     This theorem is used in the preservation proofs of the invariant."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert)
       (commtt
        (active-committee-at-round cert.round vstate.blockchain all-vals)))
    (and commtt
         (set::subset (certificate->signers cert)
                      (committee-members commtt))
         (equal (set::cardinality (certificate->signers cert))
                (committee-quorum commtt))))

  ///

  (defruled validator-signers-quorum-in-committee-p-same-blockchains
    (implies (equal (validator-state->blockchain vstate1)
                    (validator-state->blockchain vstate2))
             (equal (validator-signers-quorum-in-committee-p
                     cert vstate1 all-vals)
                    (validator-signers-quorum-in-committee-p
                     cert vstate2 all-vals)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signers-quorum-in-committee-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          every correct signer of every certificate in the system
          can calculate the committee for (the round of) the certificate,
          the committee includes all the signers,
          and the signers form a quorum in the committee."
  :long
  (xdoc::topstring
   (xdoc::p
    "The certificates in the system are
     the ones owned by any correct validator,
     which are all the same, as proved in @(see same-owned-certificates);
     so we pick an arbitrary correct @('val'),
     just to pick a certificate @('cert') from its owned set."))
  (forall (val cert signer)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (certificates-owned-by val systate))
                        (set::in signer (certificate->signers cert))
                        (set::in signer (correct-addresses systate)))
                   (validator-signers-quorum-in-committee-p
                    cert
                    (get-validator-state signer systate)
                    (all-addresses systate)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signers-quorum-in-committee-p-when-init
  :short "Establishment of the invariant:
          the invariant holds on any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially there are no certificates in the system,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (signers-quorum-in-committee-p systate))
  :enable (signers-quorum-in-committee-p
           certificates-owned-by-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signers-quorum-in-committee-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only kind of event that introduces a new certificate
     is @('create-certificate').
     All the other events leave the existing certificates unchanged,
     and so if the invariant holds in the old state
     then it also holds in the new state.
     This is easy to prove, via two theorems for each event:
     one for a single signer, and one for the system.")
   (xdoc::p
    "A @('create-certificate') event takes a little more work.
     We need a theorem for existing certificates,
     which is proved similarly to the other events.
     Then we need a theorem for the new certificate,
     which we prove from @(tsee create-certificate-possiblep)
     and the predicates it calls directly or indirectly.
     These theorems prove that the property holds in the old state,
     but we need it for the new state.
     So we use the theorem
     @('validator-signers-quorum-in-committee-p-same-blockchains')
     in @(tsee validator-signers-quorum-in-committee-p),
     to transfer the property from the old to the new state."))

  ;; create-certificate:

  (defruled
    validator-signers-quorum-in-committee-p-of-create-certificate-next-old
    (implies (and (set::in signer (certificate->signers cert1))
                  (set::in signer (correct-addresses systate))
                  (validator-signers-quorum-in-committee-p
                   cert1
                   (get-validator-state signer systate)
                   (all-addresses systate)))
             (validator-signers-quorum-in-committee-p
              cert1
              (get-validator-state
               signer (create-certificate-next cert systate))
              (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p
             validator-state->blockchain-of-create-certificate-next))

  (defruled validator-signers-quorum-in-committee-p-when-author-possiblep
    (b* ((author (certificate->author cert))
         (vstate (get-validator-state author systate)))
      (implies (create-certificate-author-possiblep
                cert vstate (all-addresses systate))
               (validator-signers-quorum-in-committee-p
                cert vstate (all-addresses systate))))
    :enable (validator-signers-quorum-in-committee-p
             create-certificate-author-possiblep
             create-certificate-signer-possiblep
             certificate->signers
             set::expensive-rules))

  (defruled validator-signers-quorum-in-committee-p-when-endorser-possiblep
    (b* ((vstate (get-validator-state endorser systate)))
      (implies (and (set::in endorser (certificate->endorsers cert))
                    (create-certificate-endorser-possiblep
                     cert vstate (all-addresses systate)))
               (validator-signers-quorum-in-committee-p
                cert vstate (all-addresses systate))))
    :enable (validator-signers-quorum-in-committee-p
             create-certificate-endorser-possiblep
             create-certificate-signer-possiblep
             certificate->signers
             set::expensive-rules))

  (defruled validator-signers-quorum-in-committee-p-when-endorsers-possiblep
    (implies (and (set::in endorser (certificate->endorsers cert))
                  (set::in endorser (correct-addresses systate))
                  (create-certificate-endorsers-possiblep cert systate))
             (validator-signers-quorum-in-committee-p
              cert
              (get-validator-state endorser systate)
              (all-addresses systate)))
    :enable (create-certificate-endorsers-possiblep
             loop-lemma)
    :prep-lemmas
    ((defruled loop-lemma
       (implies (and (set::in endorser endorsers)
                     (set::in endorser (certificate->endorsers cert))
                     (set::in endorser (correct-addresses systate))
                     (create-certificate-endorsers-possiblep-loop cert
                                                                  endorsers
                                                                  systate))
                (validator-signers-quorum-in-committee-p
                 cert
                 (get-validator-state endorser systate)
                 (all-addresses systate)))
       :induct t
       :enable
       (create-certificate-endorsers-possiblep-loop
        validator-signers-quorum-in-committee-p-when-endorser-possiblep))))

  (defruled validator-signers-quorum-in-committee-p-when-create-possiblep
    (implies (and (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate))
                  (create-certificate-possiblep cert systate))
             (validator-signers-quorum-in-committee-p
              cert
              (get-validator-state signer systate)
              (all-addresses systate)))
    :enable (create-certificate-possiblep
             certificate->signers
             validator-signers-quorum-in-committee-p-when-author-possiblep
             validator-signers-quorum-in-committee-p-when-endorsers-possiblep))

  (defruled
    validator-signers-quorum-in-committee-p-of-create-certificate-next-new
    (implies (and (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate))
                  (create-certificate-possiblep cert systate))
             (validator-signers-quorum-in-committee-p
              cert
              (get-validator-state
               signer (create-certificate-next cert systate))
              (all-addresses systate)))
    :use (:instance validator-signers-quorum-in-committee-p-same-blockchains
                    (vstate1 (get-validator-state
                              signer (create-certificate-next cert systate)))
                    (vstate2 (get-validator-state signer systate))
                    (all-vals (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p-when-create-possiblep
             validator-state->blockchain-of-create-certificate-next))

  (defruled signers-quorum-in-committee-p-of-create-certificate-next
    (implies (and (signers-quorum-in-committee-p systate)
                  (create-certificate-possiblep cert systate))
             (signers-quorum-in-committee-p
              (create-certificate-next cert systate)))
    :use (:instance lemma (cert (certificate-fix cert)))
    :prep-lemmas
    ((defruled lemma
       (implies (and (certificatep cert)
                     (signers-quorum-in-committee-p systate)
                     (create-certificate-possiblep cert systate))
                (signers-quorum-in-committee-p
                 (create-certificate-next cert systate)))
       :enable
       (signers-quorum-in-committee-p
        signers-quorum-in-committee-p-necc
        certificates-owned-by-of-create-certificate-next
        validator-signers-quorum-in-committee-p-of-create-certificate-next-new
        validator-signers-quorum-in-committee-p-of-create-certificate-next-old))))

  ;; receive-certificate:

  (defruled validator-signers-quorum-in-committee-p-of-receive-certificate-next
    (implies (and (set::in signer (certificate->signers cert1))
                  (set::in signer (correct-addresses systate))
                  (validator-signers-quorum-in-committee-p
                   cert
                   (get-validator-state signer systate)
                   (all-addresses systate))
                  (receive-certificate-possiblep msg systate))
             (validator-signers-quorum-in-committee-p
              cert
              (get-validator-state
               signer (receive-certificate-next msg systate))
              (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p
             validator-state->blockchain-of-receive-certificate-next))

  (defruled signers-quorum-in-committee-p-of-receive-certificate-next
    (implies (and (signers-quorum-in-committee-p systate)
                  (receive-certificate-possiblep msg systate))
             (signers-quorum-in-committee-p
              (receive-certificate-next msg systate)))
    :enable
    (signers-quorum-in-committee-p
     signers-quorum-in-committee-p-necc
     certificates-owned-by-of-receive-certificate-next
     validator-signers-quorum-in-committee-p-of-receive-certificate-next))

  ;; store-certificate:

  (defruled validator-signers-quorum-in-committee-p-of-store-certificate-next
    (implies (and (set::in signer (certificate->signers cert1))
                  (set::in signer (correct-addresses systate))
                  (validator-signers-quorum-in-committee-p
                   cert1
                   (get-validator-state signer systate)
                   (all-addresses systate))
                  (store-certificate-possiblep val cert systate))
             (validator-signers-quorum-in-committee-p
              cert1
              (get-validator-state
               signer (store-certificate-next val cert systate))
              (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p
             validator-state->blockchain-of-store-certificate-next))

  (defruled signers-quorum-in-committee-p-of-store-certificate-next
    (implies (and (signers-quorum-in-committee-p systate)
                  (store-certificate-possiblep val cert systate))
             (signers-quorum-in-committee-p
              (store-certificate-next val cert systate)))
    :enable
    (signers-quorum-in-committee-p
     signers-quorum-in-committee-p-necc
     certificates-owned-by-of-store-certificate-next
     validator-signers-quorum-in-committee-p-of-store-certificate-next))

  ;; advance-round:

  (defruled validator-signers-quorum-in-committee-p-of-advance-round-next
    (implies (and (set::in signer (certificate->signers cert1))
                  (set::in signer (correct-addresses systate))
                  (validator-signers-quorum-in-committee-p
                   cert1
                   (get-validator-state signer systate)
                   (all-addresses systate))
                  (advance-round-possiblep val systate))
             (validator-signers-quorum-in-committee-p
              cert1
              (get-validator-state
               signer (advance-round-next val systate))
              (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p
             validator-state->blockchain-of-advance-round-next))

  (defruled signers-quorum-in-committee-p-of-advance-round-next
    (implies (and (signers-quorum-in-committee-p systate)
                  (advance-round-possiblep val systate))
             (signers-quorum-in-committee-p
              (advance-round-next val systate)))
    :enable
    (signers-quorum-in-committee-p
     signers-quorum-in-committee-p-necc
     certificates-owned-by-of-advance-round-next
     validator-signers-quorum-in-committee-p-of-advance-round-next))

  ;; commit-anchors:

  (defruled validator-signers-quorum-in-committee-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (set::in signer (certificate->signers cert1))
                  (set::in signer (correct-addresses systate))
                  (validator-signers-quorum-in-committee-p
                   cert1
                   (get-validator-state signer systate)
                   (all-addresses systate))
                  (commit-anchors-possiblep val systate))
             (validator-signers-quorum-in-committee-p
              cert1
              (get-validator-state
               signer (commit-anchors-next val systate))
              (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p
             validator-state->blockchain-of-commit-anchors-next
             active-committee-at-round-of-extend-blockchain-no-change
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-anchors-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             blocks-last-round
             posp
             pos-fix
             evenp))

  (defruled signers-quorum-in-committee-p-of-commit-anchors-next
    (implies (and (ordered-even-p systate)
                  (last-blockchain-round-p systate)
                  (signers-quorum-in-committee-p systate)
                  (commit-anchors-possiblep val systate))
             (signers-quorum-in-committee-p
              (commit-anchors-next val systate)))
    :enable
    (signers-quorum-in-committee-p
     signers-quorum-in-committee-p-necc
     certificates-owned-by-of-commit-anchors-next
     validator-signers-quorum-in-committee-p-of-commit-anchors-next))

  ;; timer-expires:

  (defruled validator-signers-quorum-in-committee-p-of-timer-expires-next
    (implies (and (set::in signer (certificate->signers cert1))
                  (set::in signer (correct-addresses systate))
                  (validator-signers-quorum-in-committee-p
                   cert1
                   (get-validator-state signer systate)
                   (all-addresses systate))
                  (timer-expires-possiblep val systate))
             (validator-signers-quorum-in-committee-p
              cert1
              (get-validator-state
               signer (timer-expires-next val systate))
              (all-addresses systate)))
    :enable (validator-signers-quorum-in-committee-p
             validator-state->blockchain-of-timer-expires-next))

  (defruled signers-quorum-in-committee-p-of-timer-expires-next
    (implies (and (signers-quorum-in-committee-p systate)
                  (timer-expires-possiblep val systate))
             (signers-quorum-in-committee-p
              (timer-expires-next val systate)))
    :enable
    (signers-quorum-in-committee-p
     signers-quorum-in-committee-p-necc
     certificates-owned-by-of-timer-expires-next
     validator-signers-quorum-in-committee-p-of-timer-expires-next)))
