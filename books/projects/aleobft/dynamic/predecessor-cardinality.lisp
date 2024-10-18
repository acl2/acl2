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

(include-book "previous-quorum")
(include-book "backward-closure")
(include-book "unequivocal-dags")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ predecessor-cardinality
  :parents (correctness)
  :short "Invariant that the cardinality of
          the predecessor certificates of each certificate in each DAG
          is the quorum size of the active committee at that round,
          or 0 if the round is 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a consequence of the previously proved invariant
     @(see previous-quorum),
     which is about the references to the predecessor certificates,
     in the form of the authors of those certificates.")
   (xdoc::p
    "The non-equivocation of certificates in DAGs
     means that there is a bijection between
     the certificates at a round and their authors
     (since they have the same round, their authors must be distinct).
     The backward closure of the DAG means that
     there are certificates, in the predecessor round,
     for all the authors referenced by a certificate at a round.
     Putting these two things together,
     we get that the number of predecessor certificates in the DAG
     is the same as the number of references to previous certificates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-predecessor-cardinality-p ((cert certificatep)
                                             (vstate validator-statep)
                                             (all-vals address-setp))
  :guard (and (set::in cert (validator-state->dag vstate))
              (or (equal (certificate->round cert) 1)
                  (active-committee-at-round (1- (certificate->round cert))
                                             (validator-state->blockchain vstate)
                                             all-vals)))
  :returns (yes/no booleanp)
  :short "Check if the number of predecessor certificates
          of a certificate in the DAG of a validator (represented by its state)
          is the quorum number for the active committee
          at the round just before the certificate,
          or is 0 if the certificate's round is 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee predecessor-cardinality-p) to define our invariant.
     The validator whose state is @('vstate')
     is the one with the DAG and certificate.
     The guard ensures that the validator can calculate the committee."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (equal (set::cardinality (predecessors cert vstate.dag))
           (if (= cert.round 1)
               0
             (b* ((commtt (active-committee-at-round (1- cert.round)
                                                     vstate.blockchain
                                                     all-vals)))
               (committee-quorum commtt)))))
  :guard-hints (("Goal" :in-theory (enable posp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk predecessor-cardinality-p ((systate system-statep))
  :guard (accepted-certificate-committee-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each certificate in the DAG of each validator,
          the number of predecessor certificates is
          0 if the certificate's round is 1,
          or the quorum size of the committee
          at the preceding round if the certificate's round is not 1."
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (validator-state->dag
                                       (get-validator-state val systate))))
                   (validator-predecessor-cardinality-p
                    cert
                    (get-validator-state val systate)
                    (all-addresses systate))))
  :guard-hints
  (("Goal"
    :in-theory (enable accepted-certificate-committee-p-necc
                       accepted-certificates
                       posp
                       active-committee-at-previous-round-when-at-round))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection predecessor-cardinality-p-invariant
  :short "Proof of the invariant from other invariants."
  :long
  (xdoc::topstring
   (xdoc::p
    "This mainly follows from the previous quorum invariant,
     but we also need the backward closure of DAGs
     as well as the non-equivocation of DAGs;
     however, the main one is the previous quorum invariant,
     which motivates the name of this theorem.")
   (xdoc::p
    "First we prove a theorem for a single validator.
     The key rule is
     @('cardinality-of-certificates-with-authors+round-when-subset'),
     since @(tsee predecessors) is defined
     in terms of @(tsee certificates-with-authors+round).
     This rule gives us the desired equality to prove the theorem,
     but we need to discharge the hypothesis that
     the set of references to previous certificates
     is a subset of the authors of
     the certificates at the preceding round.
     This is exactly what the backward closure invariant gives us."))

  (defruled validator-predecessor-cardinality-p-when-previous-quorum
    (implies (and (validator-previous-quorum-p cert vstate all-vals)
                  (certificate-set-unequivocalp (validator-state->dag vstate))
                  (dag-closedp (validator-state->dag vstate))
                  (set::in cert (validator-state->dag vstate)))
             (validator-predecessor-cardinality-p cert vstate all-vals))
    :use (:instance dag-closedp-necc
                    (dag (validator-state->dag vstate)))
    :enable (validator-previous-quorum-p
             validator-predecessor-cardinality-p
             predecessors
             cardinality-of-certificates-with-authors+round-when-subset
             certificate-previous-in-dag-p))

  (defruled predecessor-cardinality-p-when-previous-quorum
    (implies (and (previous-quorum-p systate)
                  (unequivocal-dags-p systate)
                  (backward-closed-p systate))
             (predecessor-cardinality-p systate))
    :enable (predecessor-cardinality-p
             previous-quorum-p-necc
             unequivocal-dags-p-necc-single
             backward-closed-p-necc
             validator-predecessor-cardinality-p-when-previous-quorum
             accepted-certificates)))
