; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "reachability")
(include-book "signed-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ signer-records
  :parents (correctness)
  :short "Invariant that each correct signer of each certificate
          has a record of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "A signer of a certificate is either the author or an endorser.
     The author adds the certificate to its DAG as it creates the certificate,
     as defined in the transitions for @('create'),
     so it has a record of the certificate.
     As also defined in the transitions for @('create'),
     an endorser adds the certificate's author and round
     to the set of endorsed pairs,
     which also constitutes a record of the certificate.
     Certificate creation also broadcasts the certificate to endorsers
     (as well as to other correct validators, except the author),
     so an endorser may receive the whole certificate at some point,
     via an @('accept') event,
     which removes the author-round pair from the endorsed set,
     but which adds the whole certificate to the DAG,
     so the validator still has a record of the certificate.
     Certificates are never removed by other events.")
   (xdoc::p
    "Thus, both in the case of the author and in the case of an endorser,
     the signer in question always has a record of the certificate,
     in its own validator state, in two possible forms:
     in the DAG (the whole certificate),
     or in the set of endorsed pairs (just author and round).")
   (xdoc::p
    "It may be tempting to formalize the notion of
     `a signer having a record of a certificate'
     as the disjunction of
     (i) the certificate is in the DAG of the signer, or
     (ii) the author and round of the certificate form a pair
     in the set of endorsed pairs of the signer.
     However, this would not be quite preserved by @('accept') events.
     The validator receiving a certificate @('C')
     and storing it in the DAG
     could already have a record of a certificate @('C0'),
     different from @('C') but with the same author and round,
     i.e. @('C.author = C0.author') and @('C.round = C0.round').
     This cannot happen because of non-equivocation,
     but this property is not yet available
     at this point of this formal development,
     and in fact we need to use the notion of signer records
     to prove non-equivocation, so we cannot assume it here.
     The problem is that, upon storing a received @('C') into the DAG,
     if the record of @('C0') is in the set of endorsed pairs,
     and not in the DAG,
     the pair of the common author and round is removed from the set,
     and thus the validator no longer has a record of @('C0')
     in the sense defined by the tempting definition above,
     although it now has a record of @('C').
     So we need to weaken the notion of
     `a signer having a record of a certificate @('C')'
     to the disjunction of
     (i) the DAG of the signer has some certificate @('C\'')
     (the same as @('C') or not)
     with the author and round of @('C'),
     (ii) the author and round of @('C') form a pair
     in the set of endorsed pairs of the signer.
     That is, the notion is only about the author and signer,
     not the whole certificate.
     This is the formulation we define and prove here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signer-record-p ((author addressp)
                         (round posp)
                         (vstate validator-statep))
  :returns (yes/no booleanp)
  :short "Check if (the state of) a signer has
          a record of a certificate author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the case if
     the DAG has some certificate with the given author and round,
     or the given author and round are in the set of endorsed pairs.
     We express the first condition by saying that
     @(tsee cert-with-author+round) does not return @('nil').
     The signer is represented by its state @('vstate') here."))
  (b* (((validator-state vstate) vstate)
       (author (address-fix author))
       (round (pos-fix round)))
    (or (and (cert-with-author+round author round vstate.dag) t)
        (set::in (make-address+pos :address author :pos round)
                 vstate.endorsed)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk signer-records-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for every certificate signed by a correct validator,
          the validator has a record of that certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "We express this on the set of signed certificates
     defined by @(tsee signed-certs)."))
  (forall (signer cert)
          (implies (and (set::in signer (correct-addresses systate))
                        (set::in cert (signed-certs signer systate)))
                   (signer-record-p (certificate->author cert)
                                    (certificate->round cert)
                                    (get-validator-state signer systate))))
  ///
  (fty::deffixequiv-sk signer-records-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-records-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially, there are no signed certificates,
     so the invariant trivially holds."))
  (implies (system-initp systate)
           (signer-records-p systate))
  :enable (signer-records-p
           signed-certs-when-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection signer-records-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A @('create') event adds a new certificate
     to the set of certificates signed by each signer of the certificate.
     We prove a theorem saying that
     the author and round of the new certificate satisfy the invariant,
     which follows from the definition of the creation of the certificate,
     which adds the certificate to the author's DAG
     and the author-round pair to the endorsers' endorser sets.
     We prove another theorem saying that the old recorded certificates
     are still recorded in the new states,
     because there is no other change for those w.r.t. their records.
     Then we prove a theorem showing the preservation of the system invariant
     on all certificates after @('create'),
     via the two aforementioned theorems for new and old certificates.")
   (xdoc::p
    "For all other kinds of events, we prove two theorems:
     one is for each generic validator, and one is for the whole system.")
   (xdoc::p
    "An @('accept') event may remove an endorsed pair,
     but it also adds the certificate,
     whose author and round are the ones of the removed pair,
     to the buffer.
     So the invariant is preserved for that certificate.
     For the other certificates, the invariant is also preserved
     because nothing changes for them in terms of their records.")
   (xdoc::p
    "For the other kinds of events,
     nothing changes for any certificate in terms of its records."))

  ;; create:

  (defruled signer-record-p-of-create-next-new
    (implies (and (set::in signer (certificate->signers cert))
                  (set::in signer (correct-addresses systate)))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (create-next cert systate))))
    :enable (signer-record-p
             validator-state->dag-of-create-next
             validator-state->endorsed-of-create-next
             certificate->signers
             cert-with-author+round-of-insert-iff))

  (defruled signer-record-p-of-create-next-old
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert1)
                                   (certificate->round cert1)
                                   (get-validator-state signer systate)))
             (signer-record-p (certificate->author cert1)
                              (certificate->round cert1)
                              (get-validator-state
                               signer (create-next cert systate))))
    :enable (signer-record-p
             validator-state->dag-of-create-next
             validator-state->endorsed-of-create-next
             cert-with-author+round-of-insert-iff))

  (defruled signer-records-p-of-create-next
    (implies (signer-records-p systate)
             (signer-records-p (create-next cert systate)))
    :enable (signer-records-p
             signer-records-p-necc
             signed-certs-of-create-next
             signer-record-p-of-create-next-new
             signer-record-p-of-create-next-old))

  ;; accept:

  (defruled signer-record-p-of-accept-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (accept-possiblep msg systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (accept-next msg systate))))
    :enable (signer-record-p
             validator-state->dag-of-accept-next
             validator-state->endorsed-of-accept-next
             cert-with-author+round-of-insert-iff))

  (defruled signer-records-p-of-accept-next
    (implies (and (signer-records-p systate)
                  (accept-possiblep msg systate))
             (signer-records-p (accept-next msg systate)))
    :enable (signed-certs-of-accept-next
             signer-record-p-of-accept-next
             signer-records-p
             signer-records-p-necc))

  ;; advance:

  (defruled signer-record-p-of-advance-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (advance-possiblep val systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (advance-next val systate))))
    :enable signer-record-p)

  (defruled signer-records-p-of-advance-next
    (implies (and (signer-records-p systate)
                  (advance-possiblep val systate))
             (signer-records-p (advance-next val systate)))
    :enable (signed-certs-of-advance-next
             signer-record-p-of-advance-next
             signer-records-p
             signer-records-p-necc))

  ;; commit:

  (defruled signer-record-p-of-commit-next
    (implies (and (set::in signer (correct-addresses systate))
                  (signer-record-p (certificate->author cert)
                                   (certificate->round cert)
                                   (get-validator-state signer systate))
                  (commit-possiblep val systate))
             (signer-record-p (certificate->author cert)
                              (certificate->round cert)
                              (get-validator-state
                               signer (commit-next val systate))))
    :enable signer-record-p)

  (defruled signer-records-p-of-commit-next
    (implies (and (signer-records-p systate)
                  (commit-possiblep val systate))
             (signer-records-p (commit-next val systate)))
    :enable (signed-certs-of-commit-next
             signer-record-p-of-commit-next
             signer-records-p
             signer-records-p-necc))

  ;; all events:

  (defruled signer-records-p-of-event-next
    (implies (and (signer-records-p systate)
                  (event-possiblep event systate))
             (signer-records-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-records-p-of-events-next
  :short "Preservation of the invariant by multiple transitions."
  (implies (and (events-possiblep events systate)
                (signer-records-p systate))
           (signer-records-p (events-next events systate)))
  :induct t
  :enable (events-possiblep
           events-next))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled signer-records-p-when-reachable
  :short "The invariant holds in every reachable state."
  (implies (system-state-reachablep systate)
           (signer-records-p systate))
  :enable (system-state-reachablep
           signer-records-p-when-init)
  :prep-lemmas
  ((defrule lemma
     (implies (and (system-state-reachable-from-p systate from)
                   (signer-records-p from))
              (signer-records-p systate))
     :use (:instance
           signer-records-p-of-events-next
           (events (system-state-reachable-from-p-witness systate from))
           (systate from))
     :enable system-state-reachable-from-p)))
