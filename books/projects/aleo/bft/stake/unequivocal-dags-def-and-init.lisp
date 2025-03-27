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

(include-book "initialization")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ unequivocal-dags-def-and-init
  :parents (correctness)
  :short "Invariant that DAGs are unequivocal:
          definition and establishment."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the model of AleoBFT with static committees,
     certificates are unequivocal across the whole system,
     i.e. all the certificates in the system have
     unique combinations of author and round.
     With dynamic committees (with or without stake),
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
     according to our model of @('create').
     This equivocal certificate is broadcast to all correct validators,
     according to our model of reliable broadcast;
     and this certificate may be moved
     from the network to a receiving validator's buffer,
     via a @('receive') event.
     However, our model of @('store') events says that
     a correct validator will store a certificate into the DAG
     only if its signers form a quorum in the active committee.
     Therefore, in the hypothetical situation sketched above,
     a correct validator will not accept the equivocal certificate,
     which will forever sit in buffers or in the network,
     but will never move into any DAG.
     So this is how the non-equivocation property must be weakened:
     it must only apply to the DAG,
     which is, after all, what matters,
     since blocks are generated from DAGs.")
   (xdoc::p
    "The non-equivocation of the DAG of a single validator,
     as expressed by @(tsee certificate-set-unequivocalp)
     applied to the DAG of the validator,
     could be proved from some already proved invariants.
     However, we need the more general non-equivocation of DAGs
     across multiple validators, namely that
     if two validators have two certificates (one each) in their DAGs
     with the same author and round, then they are equal certificates.
     The latter property is expressed by @(tsee certificate-sets-unequivocalp)
     applied to the DAGs of the two validators.
     The property for two validator subsumes the property for one validator,
     by choosing the two validators to be equal.
     So there is no point in proving non-equivocation for a single validator,
     which involves some work,
     and instead we prove non-equivocation for multiple validators,
     which we need anyhow,
     and then we obtain non-equivocation for single validator
     as a very simple consequence.")
   (xdoc::p
    "However, proving DAG non-equivocation for multiple validators
     relies on another invariant,
     namely that blockchains do not fork,
     which is defined in @(see nonforking-blockchains-def-and-init).
     The reason is that we need the fact that different validators agree on
     the active committees at certain rounds;
     since the active committee is calculated from the blockchain,
     we need the fact that blockchains do not fork,
     so that the validators calculate the same committee
     (for their common blockchain prefixes).
     In turn, the non-forking of blockchains
     relies on the non-equivocation of DAG certificates.
     So the preservation of the two invariants
     must be proved at the same time by induction,
     because we need a sufficiently strong induction hypothesis,
     with both invariants in the old state available,
     from which we can prove that both invariants
     also hold on the new state.")
   (xdoc::p
    "Here we define the invariant about unequivocal DAGs
     (for multiple validators, as explained above),
     and we also prove that it holds in the initial states.
     In @(see nonforking-blockchains-def-and-init)
     we do the same for the invariant about non-forking blockchains,
     i.e. we define it and prove it holds in the initial states.
     Elsewhere we prove that each invariant holds in the new state
     if both hold in the old state,
     and finally we put everything together
     in an induction proof for both invariants
     (along with other invariants that are all inter-dependent)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk unequivocal-dags-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the DAGs of each pair of correct validators
          are mutually unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove that this invariant,
     which is defined as non-equivocation for two validators,
     implies non-equivocation for a single validator.
     This is similar to the @('-necc') rule generated by the definition,
     but it involves a single validator;
     this similarity is the reason for the name of the rule."))
  (forall (val1 val2)
          (implies (and (set::in val1 (correct-addresses systate))
                        (set::in val2 (correct-addresses systate)))
                   (certificate-sets-unequivocalp
                    (validator-state->dag
                     (get-validator-state val1 systate))
                    (validator-state->dag
                     (get-validator-state val2 systate)))))

  ///

  (fty::deffixequiv-sk unequivocal-dags-p
    :args ((systate system-statep)))

  (defruled unequivocal-dags-p-necc-single
    (implies (and (unequivocal-dags-p systate)
                  (set::in val (correct-addresses systate)))
             (certificate-set-unequivocalp
              (validator-state->dag
               (get-validator-state val systate))))
    :enable certificate-sets-unequivocalp-of-same-set-converse))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled unequivocal-dags-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, all DAGs are empty, so the invariant trivially holds."))
  (implies (system-initp systate)
           (unequivocal-dags-p systate))
  :enable (unequivocal-dags-p
           system-initp
           system-validators-initp-necc
           validator-init))
