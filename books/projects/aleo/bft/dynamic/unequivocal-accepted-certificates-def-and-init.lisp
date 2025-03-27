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

(include-book "certificates-of-validators")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-accepted-certificates-def-and-init
  :parents (correctness)
  :short "Invariant that accepted certificates are unequivocal:
          definition and establishment."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the model of AleoBFT with static committees,
     certificates are unequivocal across the whole system,
     i.e. all the certificates in the system have
     unique combinations of author and round.
     With our current model of dynamic committees,
     this property must be weakened slightly in order to be proved.
     The reason is that, in our model, the system always includes
     all possible validators that may form committees.
     Consider, for simplicity, the first few rounds, and the genesis committee.
     Even with the fault tolerance assumptions
     formalized in @(see fault-tolerance),
     there may well be a set of faulty validators,
     outside the genesis committee,
     who sign a new certificate that has
     the same author and round as an existing certificate,
     the latter having been properly created by the genesis committee.
     This event is perfectly possible
     according to our model of @('create-certificate').
     This equivocal certificate is broadcast to all correct validators,
     according to our model of reliable broadcast.
     However, our model of @('receive-certificate') says that
     a correct validator will accept a certificate
     only if its signers form a quorum in the active committee.
     Therefore, in the hypothetical situation sketched above,
     a correct validator will not accept the equivocal certificate,
     which will forever sit in the network,
     replicated in several messages (one per correct validator),
     but will never move from the network to a validator state.
     So this is how the non-equivocation property must be weakened:
     it must only apply to the set of accepted certificates,
     i.e. the ones in DAG and buffer; see @(tsee accepted-certificates).")
   (xdoc::p
    "The non-equivocation of
     the set of certificates accepted by a single validator,
     as expressed by @(tsee certificate-set-unequivocalp)
     applied to @(tsee accepted-certificates)
     applied to the validator,
     can be proved from some already proved invariants.
     However, to prove further correctness properties of the protocol,
     we need the more general non-equivocation of
     the sets of certificates accepted by multiple validators,
     namely that if two validators accept two certificates (one each)
     with the same author and round, then they are equal certificates.
     The latter property is expressed by @(tsee certificate-sets-unequivocalp)
     applied to @(tsee accepted-certificates)
     applied to the two validators.
     The property for two validator subsumes the property for one validator,
     by choosing the two validators to be equal.
     So there is no point in proving non-equivocation for a single validator,
     which involves some work,
     and instead we prove non-equivocation for multiple validators,
     which we need anyhow,
     and then we obtain non-equivocation for single validator
     as a very simple consequence.")
   (xdoc::p
    "However, proving non-equivocation for multiple validators
     relies on another invariant,
     namely that blockchains do not fork,
     which is defined in @(see nonforking-blockchains-def-and-init).
     The reason is that we need the fact that different validators agree on
     the active committees at certain rounds;
     since the active committee is calculated from the blockchain,
     we need the fact that blockchains do not fork,
     so that they calculate the same committee
     (for their common blockchain prefixes).
     In turn, the non-forking of blockchains
     relies on the non-equivocation of certificates.
     So the preservation of the two invariants
     must be proved at the same time by induction,
     because we need a sufficiently strong induction hypothesis,
     with both invariants in the old state available,
     from which we can prove that both invariants
     also hold on the new state.")
   (xdoc::p
    "Here we define the invariant about unequivocal certificates
     (for multiple validators),
     and we also prove that it holds in the initial states.
     In @(see nonforking-blockchains-def-and-init)
     we do the same for the invariant about non-forking blockchains,
     i.e. we define it and prove it holds in the initial states.
     Then we prove that each holds in the new state
     if both hold in the old state,
     and finally we put everything together
     in an induction proof for both invariants."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequivocal-accepted-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the sets of certificates accepted by each pair of correct validators
          are mutually unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that this invariant,
     which is defined as non-equivocation for two validators,
     implies non-equivocation for a single validator.
     This is similar to the @('-necc') rule generated by the definition,
     but it involves a single validator;
     this similarity is the reason for the name of the rule.")
   (xdoc::p
    "We also prove that the invariant implies the non-equivocation of
     the DAGs of two (possibly different) validators,
     and the DAG of one validator.
     These are simple consequences of the invariant,
     since DAGs are subsets of the accepted certificates."))
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (certificate-sets-unequivocalp
                    (accepted-certificates val1 systate)
                    (accepted-certificates val2 systate))))

  ///

  (fty::deffixequiv-sk unequivocal-accepted-certificates-p
    :args ((systate system-statep)))

  (defruled unequivocal-accepted-certificates-p-necc-single
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (set::in val (correct-addresses systate)))
             (certificate-set-unequivocalp
              (accepted-certificates val systate)))
    :enable certificate-sets-unequivocalp-of-same-set-converse)

  (defruled certificate-set-unequivocalp-when-unequivocal-accepted
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (set::in val (correct-addresses systate)))
             (certificate-set-unequivocalp
              (validator-state->dag (get-validator-state val systate))))
    :disable unequivocal-accepted-certificates-p
    :use unequivocal-accepted-certificates-p-necc-single
    :enable (accepted-certificates
             certificate-set-unequivocalp-when-subset))

  (defruled certificate-sets-unequivocalp-when-unequivocal-accepted
    (implies (and (unequivocal-accepted-certificates-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in val2 (correct-addresses systate)))
             (certificate-sets-unequivocalp
              (validator-state->dag (get-validator-state val1 systate))
              (validator-state->dag (get-validator-state val2 systate))))
    :disable unequivocal-accepted-certificates-p
    :use unequivocal-accepted-certificates-p-necc
    :enable (accepted-certificates
             certificate-sets-unequivocalp-when-subsets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-accepted-certificates-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no accepted certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (unequivocal-accepted-certificates-p systate))
  :enable (unequivocal-accepted-certificates-p
           accepted-certificates-when-init
           certificate-sets-unequivocalp-when-emptyp))
