; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "operations-fault-tolerance")
(include-book "invariant-signers-have-author-round")
(include-book "invariant-signers-are-quorum")

(local (include-book "lib-ext"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-unequivocal-certificates
  :parents (correctness)
  :short "Invariant that certificates have unique author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a critical property of AleoBFT:
     each certificate is uniquely identified by its author and round,
     i.e. no two distinct certificates may have the same author and round.
     Given the separately proved "
    (xdoc::seetopic "invariant-same-certificates"
                    "invariant that validators have the same certificates")
    ", it suffices to prove this property for
     the set of certificates of a single validator,
     since it is the same set for all validators.")
   (xdoc::p
    "The intuitive argument is that
     each certificate is signed (authored and endorsed)
     by a quorum of validators.
     In order for two different certificates with the same author and round
     to exist,
     a quorum @($n - F$) of validators must have signed both.
     But since there are only @($n$) validators,
     the intersection of any two sets of @($n - F$) validators
     has at least @($F + 1$) validators,
     and therefore there is at least one correct validator in that set.
     But a correct validator would not have signed two different certificates
     with the same author and round.")
   (xdoc::p
    "Turning the above intuitive argument into an ACL2 proof
     takes a bit of work, explained below as we develop the proof.
     New certificates are created only by @('create-certificate') events,
     so it suffices to prove that each such new certificate
     must have different author or round from all the existing ones.
     This involves showing that,
     if the new certificate has the same author and round
     as an existing certificate,
     then the @('create-certificate') is actually not possible,
     because it requires some correct validator to
     both have signed the old one,
     and thus having a record of that author-round pair,
     and have not signed the new one yet,
     and thus not having a record of that same author-round pair,
     which is an impossibility.
     For the other kinds of events, the proof is easy,
     because no new certificates are created."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-unequivocal-certificates-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          if any two certificates have the same author and round,
          they are the same certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pick an arbitrary correct validator
     for getting the set of certificates in the system.
     The choice does not matter, because of the invariant that
     all correct validators have the same certificates."))
  (forall (val cert1 cert2)
          (implies (and (set::in val
                                 (correct-addresses systate))
                        (set::in cert1
                                 (certificates-for-validator val systate))
                        (set::in cert2
                                 (certificates-for-validator val systate))
                        (equal (certificate->author cert1)
                               (certificate->author cert2))
                        (equal (certificate->round cert1)
                               (certificate->round cert2)))
                   (equal cert1 cert2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-when-system-state-initp
  :short "Estalishment of the invariant:
          the invariant holds on any initial system state."
  (implies (system-state-initp systate)
           (system-unequivocal-certificates-p systate))
  :enable (system-state-initp
           system-unequivocal-certificates-p
           certificates-for-validator
           get-network-state
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-unequivocal-certificates-p-of-create-certificate-next
  :short "Preservation of the invariant by @('create-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a number of local functions and theorems,
     culminating with the (non-local) desired main theorem.")
   (xdoc::p
    "The key property, proved just before the main theorem,
     is @('not-create-certificate-possiblep-when-existing-author+round'),
     i.e. that, if the system is fault-tolerant
     (i.e. @(tsee fault-tolerant-p) holds),
     and assuming some separately proved invariants,
     if the new certificate in the @('create-certificate') event
     has the same author and round as
     some old certificate already in the system
     (i.e. in the @(tsee certificates-for-validator) set
     of some correct validator @('val')),
     then @(tsee create-certificate-possiblep) does not hold.
     This key theorem suffices to then prove the main theorem,
     with some additional structural hints for the quantification:
     the proof of that main theorem will consider all pairs of certificates,
     both involving the new one or not,
     taking care of all cases automatically
     except for the case of an old certificate and the new certificate,
     which is where the key property,
     which takes a bit of work to prove,
     comes into play.")
   (xdoc::p
    "The key property is proved by showing that
     the old certificate has a quorum of signers,
     and so does the new certificate.
     When we intersect these two sets of signers,
     given that the signers are all validators in the system,
     the intersection must have more than @(tsee max-faulty) elements.
     So one of them must be correct.
     To explicate this reasoning in a form suitable for the prover,
     we define a function that picks, from a set of validator addresses,
     the first one (if any) that is a correct validator
     (or @('nil') if none is found).
     We show that under our hypotheses,
     when this function is applied to
     the intersection of the signers of old and new certificate,
     this indeed returns a correct validator (not @('nil')).
     Then we use our hypotheses to show that this picked validator
     both has the author and round of (both) certificates,
     due to the old certificate being in the system,
     and does not have the author and round of (both) certificates,
     due to the new certificate claiming
     to satisfy @(tsee create-certificate-possiblep).
     This is an impossibility, so some of the hypotheses are inconsistent:
     we designate the @(tsee create-certificate-possiblep)
     as the one causing the inconsistency,
     so we put its negation in the conclusion of the key theorem,
     which is then used as a rewrite rule
     in the proof of the main theorem."))

  ;; Most of the local theorems below are enabled.
  ;; The disabled ones are the ones used in :USE hints,
  ;; to avoid having to disable them explicitly when the :USE hints are used.

  ;; The signers of both the old and new certificates are validators.
  ;; For the old certificate, this follows from
  ;; the SYSTEM-SIGNERS-ARE-VALIDATORS-P invariant.
  ;; For the new certificate, this follows from
  ;; the definition of CREATE-CERTIFICATE-POSSIBLEP.

  (defrulel old-certificate-signers-are-validators
    (implies (and (system-signers-are-validators-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-for-validator val systate)))
             (set::subset (certificate->signers cert)
                          (all-addresses systate)))
    :use system-signers-are-validators-p-necc
    :enable certificate-signers-are-validators-p)

  (defrulel create-certificate-signers-are-validators
    (implies (create-certificate-possiblep new-cert systate)
             (set::subset (certificate->signers new-cert)
                          (all-addresses systate)))
    :enable (create-certificate-possiblep
             certificate->signers))

  ;; The signers of both the old and new certificates form a quorum.
  ;; For the old certificate, this follows from
  ;; the SYSTEM-SIGNERS-ARE-QUORUM-P invariant.
  ;; For the new certificate, this follows from
  ;; the definition of CREATE-CERTIFICATE-POSSIBLEP.

  (defrulel old-certificate-signers-form-quorum
    (implies (and (system-signers-are-quorum-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-for-validator val systate)))
             (equal (set::cardinality (certificate->signers cert))
                    (quorum systate)))
    :enable system-signers-are-quorum-p-necc)

  (defrulel create-certificate-signers-form-quorum
    (implies (create-certificate-possiblep new-cert systate)
             (equal (set::cardinality (certificate->signers new-cert))
                    (quorum systate)))
    :enable (create-certificate-possiblep
             certificate->signers
             set::expensive-rules))

  ;; We introduce a function that returns
  ;; the common signers of two certificates.
  ;; It is just an abbreviation,
  ;; but it makes some subsequent things a bit more readable.

  (local
   (defund common-signers (cert1 cert2)
     (set::intersect (certificate->signers cert1)
                     (certificate->signers cert2))))

  ;; If the signers of two certificates are validators,
  ;; so are the common signers of the two certificates.

  (defrulel common-signers-are-validators
    (implies (and (set::subset (certificate->signers cert1)
                               (all-addresses systate))
                  (set::subset (certificate->signers cert2)
                               (all-addresses systate)))
             (set::subset (common-signers cert1 cert2)
                          (all-addresses systate)))
    :enable (common-signers
             set::expensive-rules))

  ;; Since the union of two sets of validators is also a set of validators,
  ;; its cardinality is limited by the number of validators.
  ;; We need this fact to prove the next one after this.

  (defrulel cardinality-of-union-of-validators
    (implies (and (set::subset vals1 (all-addresses systate))
                  (set::subset vals2 (all-addresses systate)))
             (<= (set::cardinality (set::union vals1 vals2))
                 (number-validators systate)))
    :rule-classes :linear
    :enable number-validators
    :disable set::expand-cardinality-of-union)

  ;; This is the core of the quorum intersection argument.
  ;; Given two sets of validators, each forming a quorum,
  ;; their intersection is strictly larger than
  ;; the maximum number of faulty validators.
  ;; Using |X| for the cardinality of a set X,
  ;; we start from the known fact that
  ;;   |A union B| = |A| + |B| - |A intersect B|
  ;; from which we get
  ;;   |A intersect B| = |A| + |B| - |A union B|
  ;; Using n for the total number of validators
  ;; and f for the maximum number of faulty validators,
  ;; the quorum is n - f, which we substitute in the equation above to get
  ;;   |A intersect B| = 2n - 2f - |A union B|
  ;; But we proved just above that
  ;;   |A union B| <= n
  ;; that is
  ;;   - |A union B| >= -n
  ;; and if we use that in the equation above we get
  ;;   |A intersect B| >= 2n - 2f - n = n - 2f
  ;; Since f < n/3, we have n > 3f, which we substitute above obtaining
  ;;   |A intersect B| >= 2n - 2f - n = n - 2f > 3f - f = f
  ;; So we get |A intersect B| > f.
  ;; There is an implicit assumption, namely that n > 0,
  ;; otherwise f = n = 0 and f = n/3 (not f < n/3),
  ;; so we need the (equivalent) hypothesis that
  ;; the set of validators is not empty.
  ;; ACL2's built-in arithmetic takes care of the reasoning detailed above,
  ;; when fed the appropriate facts;
  ;; in particular, it does not conjure up to use the n > 3f inequality,
  ;; and so we need to pass that as a :USE hint
  ;; (it being a linear rule does not suffice).
  ;; We also need to disable SET::EXPAND-CARDINALITY-OF-UNION,
  ;; because we need SET::EXPAND-CARDINALITY-OF-INTERSECT instead.

  (defruledl intersection-gt-max-faulty
    (implies (and (not (set::emptyp (all-addresses systate)))
                  (set::subset vals1 (all-addresses systate))
                  (set::subset vals2 (all-addresses systate))
                  (equal (set::cardinality vals1) (quorum systate))
                  (equal (set::cardinality vals2) (quorum systate)))
             (> (set::cardinality (set::intersect vals1 vals2))
                (max-faulty systate)))
    :rule-classes :linear
    :enable (set::expand-cardinality-of-intersect
             quorum)
    :use (number-validators-lower-bound-wrt-max-faulty)
    :disable (set::expand-cardinality-of-union
              number-validators-lower-bound-wrt-max-faulty))

  ;; We can now transfer the property just proved
  ;; to the common signers of the old and new certificates.

  (defrulel common-signers-gt-max-faulty
    (implies (and (system-signers-are-quorum-p systate)
                  (system-signers-are-validators-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-for-validator val systate))
                  (create-certificate-possiblep new-cert systate))
             (> (set::cardinality (common-signers cert new-cert))
                (max-faulty systate)))
    :rule-classes :linear
    :enable (common-signers
             nonempty-all-addresses-when-correct-validator)
    :use (:instance intersection-gt-max-faulty
                    (vals1 (certificate->signers cert))
                    (vals2 (certificate->signers new-cert))))

  ;; Now we need to pick a correct validator from this set.
  ;; We define a more general function to pick
  ;; a correct validator from a set of validator addresses.
  ;; This function returns NIL if there is no correct validator in the set.

  (local
   (defund pick-correct-validator (vals systate)
     (b* (((when (set::emptyp vals)) nil)
          (val (set::head vals))
          ((when (set::in val (correct-addresses systate))) val))
       (pick-correct-validator (set::tail vals) systate))))

  ;; Now we prove some properties of this function.
  ;; First, if the function does not return nil,
  ;; it returns a validator in the set,
  ;; and in fact a correct one in the system.

  (defrulel pick-correct-validator-in-vals-when-not-nil
    (implies (pick-correct-validator vals systate)
             (set::in (pick-correct-validator vals systate) vals))
    :induct t
    :enable pick-correct-validator)

  (defrulel pick-correct-validator-is-correct-validator-when-not-nil
    (implies (pick-correct-validator vals systate)
             (set::in (pick-correct-validator vals systate)
                      (correct-addresses systate)))
    :induct t
    :enable pick-correct-validator)

  ;; If the function returns NIL,
  ;; all the validators in the set must be faulty.

  (defruledl all-faulty-validators-when-not-pick-correct-validator
    (implies (and (set::subset vals (all-addresses systate))
                  (not (pick-correct-validator vals systate)))
             (set::subset vals (faulty-addresses systate)))
    :induct t
    :enable (pick-correct-validator
             faulty-addresses
             set::expensive-rules
             not-nil-in-correct-addresses))

  ;; Therefore, if the system is fault-tolerant,
  ;; and the set has more elements than @(tsee max-faulty),
  ;; the function must not return NIL.
  ;; That is, it must return a correct validator address.

  (defrulel pick-correct-validator-when-fault-tolerant-p
    (implies (and (set::subset vals (all-addresses systate))
                  (fault-tolerant-p systate)
                  (> (set::cardinality vals)
                     (max-faulty systate)))
             (pick-correct-validator vals systate))
    :enable (fault-tolerant-p
             number-faulty)
    :use (:instance all-faulty-validators-when-not-pick-correct-validator))

  ;; To derive the contradiction,
  ;; we need to show that the common signer picked by the function above
  ;; both has the author-round pair and does not have the author-round pair.
  ;; We first prove that any signer of the old certificate has the pair,
  ;; and that any signer of the new certificate does not have it.

  (defrulel old-signer-has-author+round
    (implies (and (system-signers-have-author+round-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-for-validator val systate))
                  (set::in signer (certificate->signers cert)))
             (signer-has-author+round-p signer
                                        (certificate->author cert)
                                        (certificate->round cert)
                                        systate))
    :enable system-signers-have-author+round-p-necc)

  (defruledl new-signer-does-not-have-author+round
    (implies (and (create-certificate-possiblep new-cert systate)
                  (set::in signer (certificate->signers new-cert)))
             (signer-does-not-have-author+round-p signer
                                                  (certificate->author new-cert)
                                                  (certificate->round new-cert)
                                                  systate))
    :enable (create-certificate-possiblep
             signers-do-not-have-author+round-p-element))

  ;; We also show that, for correct validators,
  ;; having and not having the pair are incompatible assertions:
  ;; if a validator has the pair, then it does not not have the pair
  ;; (the repetition of 'not not' is intentional).

  (defrulel not-no-author+round-when-author+round
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-has-author+round-p signer author cert systate))
             (not (signer-does-not-have-author+round-p
                   signer author cert systate)))
    :enable (signer-has-author+round-p
             signer-does-not-have-author+round-p))

  ;; We finally need to know that if a validator is a common signer,
  ;; then it is a signer of both certificates.

  (defruledl in-both-signers-if-in-common-signers
    (implies (set::in val (common-signers cert1 cert2))
             (and (set::in val (certificate->signers cert1))
                  (set::in val (certificate->signers cert2))))
    :enable common-signers)

  ;; This is the key property mentioned in the proof overview earlier.
  ;; Assuming fault tolerance, and given separately proved invariants,
  ;; if the new certificate has the same author and round
  ;; as some old certificate,
  ;; then the CREATE-CERTIFICATE event is not possible.
  ;; We need to tell the prover, in the :USE hints,
  ;; to pick a correct validator from the common signers of the certificates,
  ;; via the functions defined above.
  ;; Given the properties of those functions proved above,
  ;; and with a few hints, the theorem is proved.

  (defrulel not-create-certificate-possiblep-when-existing-author+round
    (implies (and (fault-tolerant-p systate)
                  (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in cert (certificates-for-validator val systate))
                  (certificatep new-cert)
                  (equal (certificate->author new-cert)
                         (certificate->author cert))
                  (equal (certificate->round new-cert)
                         (certificate->round cert)))
             (not (create-certificate-possiblep new-cert systate)))
    :use ((:instance in-both-signers-if-in-common-signers
                     (val (pick-correct-validator (common-signers cert new-cert)
                                                  systate))
                     (cert1 cert)
                     (cert2 new-cert))
          (:instance new-signer-does-not-have-author+round
                     (signer
                      (pick-correct-validator (common-signers cert new-cert)
                                              systate)))))

  ;; This is the main (non-local) theorem,
  ;; which asserts the preservation of the invariant
  ;; by CREATE-CERTIFICATE events.
  ;; The hints are structural,
  ;; typical when there are universal quantifications in ACL2:
  ;; we expand the universal quantification in the conclusion,
  ;; which generates the arbitrary witnesses,
  ;; and we use the '-NECC' property
  ;; of the universal quantification in the hypothesis
  ;; (it does not just apply as a rewrite rule).
  ;; Behind the scenes, the rewrite rule
  ;; NOT-CREATE-CERTIFICATE-POSSIBLEP-WHEN-EXISTING-AUTHOR+ROUND
  ;; proved just above applies,
  ;; resolving the non-trivial case of the proof below.

  (defrule system-unequivocal-certificates-p-of-create-certificate-next
    (implies (and (system-unequivocal-certificates-p systate)
                  (system-signers-are-validators-p systate)
                  (system-signers-are-quorum-p systate)
                  (system-signers-have-author+round-p systate)
                  (fault-tolerant-p systate)
                  (create-certificate-possiblep cert systate)
                  (certificatep cert))
             (system-unequivocal-certificates-p
              (create-certificate-next cert systate)))
    :expand (system-unequivocal-certificates-p
             (create-certificate-next cert systate))
    :use (:instance system-unequivocal-certificates-p-necc
                    (val
                     (mv-nth 0 (system-unequivocal-certificates-p-witness
                                (create-certificate-next cert systate))))
                    (cert1
                     (mv-nth 1 (system-unequivocal-certificates-p-witness
                                (create-certificate-next cert systate))))
                    (cert2
                     (mv-nth 2 (system-unequivocal-certificates-p-witness
                                (create-certificate-next cert systate)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-of-receive-certificate-next
  :short "Preservation of the invariant by @('receive-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-unequivocal-certificates-p systate)
                (receive-certificate-possiblep msg systate))
           (system-unequivocal-certificates-p
            (receive-certificate-next msg systate)))
  :expand (system-unequivocal-certificates-p
           (receive-certificate-next msg systate))
  :use (:instance system-unequivocal-certificates-p-necc
                  (val
                   (mv-nth 0 (system-unequivocal-certificates-p-witness
                              (receive-certificate-next msg systate))))
                  (cert1
                   (mv-nth 1 (system-unequivocal-certificates-p-witness
                              (receive-certificate-next msg systate))))
                  (cert2
                   (mv-nth 2 (system-unequivocal-certificates-p-witness
                              (receive-certificate-next msg systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-of-store-certificate-next
  :short "Preservation of the invariant by @('store-certificate') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-unequivocal-certificates-p systate)
                (store-certificate-possiblep cert val systate))
           (system-unequivocal-certificates-p
            (store-certificate-next cert val systate)))
  :expand (system-unequivocal-certificates-p
           (store-certificate-next cert val systate))
  :use (:instance system-unequivocal-certificates-p-necc
                  (val
                   (mv-nth 0 (system-unequivocal-certificates-p-witness
                              (store-certificate-next cert val systate))))
                  (cert1
                   (mv-nth 1 (system-unequivocal-certificates-p-witness
                              (store-certificate-next cert val systate))))
                  (cert2
                   (mv-nth 2 (system-unequivocal-certificates-p-witness
                              (store-certificate-next cert val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-of-advance-round-next
  :short "Preservation of the invariant by @('advance-round') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-unequivocal-certificates-p systate)
                (advance-round-possiblep val systate))
           (system-unequivocal-certificates-p
            (advance-round-next val systate)))
  :expand (system-unequivocal-certificates-p
           (advance-round-next val systate))
  :use (:instance system-unequivocal-certificates-p-necc
                  (val
                   (mv-nth 0 (system-unequivocal-certificates-p-witness
                              (advance-round-next val systate))))
                  (cert1
                   (mv-nth 1 (system-unequivocal-certificates-p-witness
                              (advance-round-next val systate))))
                  (cert2
                   (mv-nth 2 (system-unequivocal-certificates-p-witness
                              (advance-round-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-of-commit-anchors-next
  :short "Preservation of the invariant by @('commit-anchors') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-unequivocal-certificates-p systate)
                (commit-anchors-possiblep val systate))
           (system-unequivocal-certificates-p
            (commit-anchors-next val systate)))
  :expand (system-unequivocal-certificates-p
           (commit-anchors-next val systate))
  :use (:instance system-unequivocal-certificates-p-necc
                  (val
                   (mv-nth 0 (system-unequivocal-certificates-p-witness
                              (commit-anchors-next val systate))))
                  (cert1
                   (mv-nth 1 (system-unequivocal-certificates-p-witness
                              (commit-anchors-next val systate))))
                  (cert2
                   (mv-nth 2 (system-unequivocal-certificates-p-witness
                              (commit-anchors-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-of-timer-expires-next
  :short "Preservation of the invariant by @('timer-expires') events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of event does not introduce new certificates,
     so the proof is easy."))
  (implies (and (system-unequivocal-certificates-p systate)
                (timer-expires-possiblep val systate))
           (system-unequivocal-certificates-p
            (timer-expires-next val systate)))
  :expand (system-unequivocal-certificates-p
           (timer-expires-next val systate))
  :use (:instance system-unequivocal-certificates-p-necc
                  (val
                   (mv-nth 0 (system-unequivocal-certificates-p-witness
                              (timer-expires-next val systate))))
                  (cert1
                   (mv-nth 1 (system-unequivocal-certificates-p-witness
                              (timer-expires-next val systate))))
                  (cert2
                   (mv-nth 2 (system-unequivocal-certificates-p-witness
                              (timer-expires-next val systate))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule system-unequivocal-certificates-p-of-event-next
  :short "Preservation of the invariant by all events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from the theorems about the various kinds of events.")
   (xdoc::p
    "We need to include the (separately proved) invariants
     needed for @('create-certificate') events as hypotheses here."))
  (implies (and (system-unequivocal-certificates-p systate)
                (system-signers-are-validators-p systate)
                (system-signers-are-quorum-p systate)
                (system-signers-have-author+round-p systate)
                (fault-tolerant-p systate)
                (event-possiblep event systate))
           (system-unequivocal-certificates-p
            (event-next event systate)))
  :enable (event-possiblep
           event-next))
