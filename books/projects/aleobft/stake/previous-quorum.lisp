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

(include-book "backward-closure")
(include-book "dag-committees")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ previous-quorum
  :parents (correctness)
  :short "Invariant that each certificate in a DAG
          has references to previous certificates
          that form a quorum in the committee in the previous,
          unless the round is 1,
          in which case there are no references to previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "When a new certificate is created via a @('create') event,
     that event's preconditions require that the certificate includes
     a quorum of references to certificates in the previous round,
     unless the certificate round is 1,
     in which case there must be no references.")
   (xdoc::p
    "When a certificate is stored into the DAG via a @('store') event,
     that event's preconditions impose a similar requirements.")
   (xdoc::p
    "Thus, all the certificates in a validator's DAG satisfy that requirement.
     The other events do not modify DAGs.")
   (xdoc::p
    "The names for this invariant,
     i.e. this XDOC topic as well as the function and theorem names,
     just mention `quorum' for brevity,
     even though that does not apply to round 1.
     But rounds greater than 1 are the ``normal'' case,
     while round 1 is a special case."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define validator-previous-quorum-p ((cert certificatep)
                                     (vstate validator-statep))
  :guard (or (equal (certificate->round cert) 1)
             (active-committee-at-round (1- (certificate->round cert))
                                        (validator-state->blockchain vstate)))
  :returns (yes/no booleanp)
  :short "Check if either a certificate has round 1
          and it has no references to previous certificates,
          or the round is not 1 and
          the certificate's references to previous certificates
          are in the committee for the round just before the certificate round
          and form a quorum in that committee,
          where the committee is calculated by a validator
          (represented by its state)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee previous-quorum-p) to define our invariant.
     The validator whose state is @('vstate') is
     the one that has the accepted certificate.
     The guard ensures that the validator can calculate the committee.")
   (xdoc::p
    "We prove a theorem about the predecessors of @('cert'),
     which we use to prove @(tsee dag-predecessor-quorum-p)
     from @(tsee previous-quorum-p) later.
     The theorem says that, under the invariant, for certificates after round 1,
     the stake of the authors of the predecessor certificates
     is at least the quorum stake for the committee at the previous round.
     This is the case under the backward closure hypothesis
     (which is an already proved invariant):
     the authors of the predecessors are
     exactly the previous certificate references (addresses) in the certificate.
     Without the backward closure hypothesis,
     the authors of the predecessors are the intersection of
     the previous reference authors
     and the authors of the certificates actually present in the previous round;
     the closure tells us the the former is a subset of the latter,
     which simplifies the intersection."))
  (b* (((validator-state vstate) vstate)
       ((certificate cert) cert))
    (if (= cert.round 1)
        (set::emptyp cert.previous)
      (b* ((commtt
            (active-committee-at-round (1- cert.round) vstate.blockchain)))
        (and (set::subset cert.previous
                          (committee-members commtt))
             (>= (committee-members-stake cert.previous commtt)
                 (committee-quorum-stake commtt))))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled predecessor-quorum-when-validator-previous-quorum-p
    (implies (and (validator-previous-quorum-p cert vstate)
                  (certificate-previous-in-dag-p
                   cert (validator-state->dag vstate))
                  (not (equal (certificate->round cert) 1)))
             (b* ((commtt (active-committee-at-round
                           (1- (certificate->round cert))
                           (validator-state->blockchain vstate))))
               (>= (committee-members-stake
                    (certificate-set->author-set
                     (predecessors cert (validator-state->dag vstate)))
                    commtt)
                   (committee-quorum-stake commtt))))
    :enable (predecessors
             certs-with-authors+round-to-authors-of-round
             certificate-set->author-set-of-certs-with-authors
             certificate-previous-in-dag-p
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk previous-quorum-p ((systate system-statep))
  :guard (dag-committees-p systate)
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          for each certificate accepted by a validator,
          either the certificate's round is 1
          and the certificate has no references to previous certificates,
          or the certificate's round is not 1
          and the references to previous certificates
          form a quorum in the committee of
          the preceding round of the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This invariant, along with backward closure and non-equivocation,
     guarantees that @(tsee dag-predecessor-quorum-p) holds, as we prove here.
     The key lemma is
     @('predecessor-quorum-when-validator-previous-quorum-p')
     proved in @(tsee validator-previous-quorum-p).
     Here we just need to enable some rules
     to establish the hypotheses of that lemma."))
  (forall (val cert)
          (implies (and (set::in val (correct-addresses systate))
                        (set::in cert (validator-state->dag
                                       (get-validator-state val systate))))
                   (validator-previous-quorum-p
                    cert
                    (get-validator-state val systate))))
  :guard-hints
  (("Goal"
    :in-theory (enable dag-committees-p-necc
                       dag-has-committees-p-necc-bind-dag
                       active-committee-at-previous-round-when-at-round )))

  ///

  (fty::deffixequiv-sk previous-quorum-p
    :args ((systate system-statep)))

  (defruled dag-predecessor-quorum-p-when-previous-quorum-p
    (implies (and (previous-quorum-p systate)
                  (backward-closed-p systate)
                  (set::in val (correct-addresses systate)))
             (dag-predecessor-quorum-p
              (validator-state->dag (get-validator-state val systate))
              (validator-state->blockchain (get-validator-state val systate))))
    :enable (predecessor-quorum-when-validator-previous-quorum-p
             dag-predecessor-quorum-p
             backward-closed-p-necc
             dag-closedp-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled previous-quorum-p-when-init
  :short "Establishment of the invariant:
          the invariant holds in any initial system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Initially all the DAGs are empty,
     so the universal quantification is trivially true."))
  (implies (system-initp systate)
           (previous-quorum-p systate))
  :enable (previous-quorum-p
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection previous-quorum-p-of-next
  :short "Preservation of the invariant:
          if the invariant holds in a system state,
          it also holds in the next system state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The proofs are somewhat analogous to @(see signer-quorum-p-of-next):
     see that documentation."))

  ;; create:

  (defruled validator-previous-quorum-p-of-create-next-old
    (implies (validator-previous-quorum-p
              cert1
              (get-validator-state val systate))
             (validator-previous-quorum-p
              cert1
              (get-validator-state val (create-next cert systate))))
    :enable (validator-previous-quorum-p
             validator-state->blockchain-of-create-next
             certificate->author-of-path-to-author+round))

  (defruled validator-previous-quorum-p-of-create-next-new
    (implies (and (create-possiblep cert systate)
                  (set::in (certificate->author cert)
                           (correct-addresses systate)))
             (validator-previous-quorum-p
              cert
              (get-validator-state (certificate->author cert)
                                   (create-next cert systate))))
    :enable (validator-previous-quorum-p
             create-possiblep
             create-author-possiblep
             create-signer-possiblep
             certificate->signers))

  (defruled previous-quorum-p-of-create-next
    (implies (and (previous-quorum-p systate)
                  (create-possiblep cert systate))
             (previous-quorum-p (create-next cert systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-state->dag-of-create-next
             validator-previous-quorum-p-of-create-next-old
             validator-previous-quorum-p-of-create-next-new))

  ;; receive:

  (defruled validator-previous-quorum-p-of-receive-next
    (implies (and (validator-previous-quorum-p
                   cert
                   (get-validator-state val systate))
                  (receive-possiblep msg systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state val (receive-next msg systate))))
    :enable validator-previous-quorum-p)

  (defruled previous-quorum-p-of-receive-next
    (implies (and (previous-quorum-p systate)
                  (receive-possiblep msg systate))
             (previous-quorum-p (receive-next msg systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-receive-next))

  ;; store:

  (defruled validator-previous-quorum-p-of-store-next-old
    (implies (and (validator-previous-quorum-p
                   cert1
                   (get-validator-state val1 systate))
                  (store-possiblep val cert systate))
             (validator-previous-quorum-p
              cert1
              (get-validator-state val1 (store-next val cert systate))))
    :enable (validator-previous-quorum-p))

  (defruled validator-previous-quorum-p-of-store-next-new
    (implies (store-possiblep val cert systate)
             (validator-previous-quorum-p
              cert
              (get-validator-state val (store-next val cert systate))))
    :enable (validator-previous-quorum-p
             store-possiblep))

  (defruled previous-quorum-p-of-store-next
    (implies (and (previous-quorum-p systate)
                  (store-possiblep val cert systate)
                  (addressp val))
             (previous-quorum-p (store-next val cert systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-state->dag-of-store-next
             validator-previous-quorum-p-of-store-next-old
             validator-previous-quorum-p-of-store-next-new))

  ;; advance:

  (defruled validator-previous-quorum-p-of-advance-next
    (implies (and (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (advance-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state val1 (advance-next val systate))))
    :enable validator-previous-quorum-p)

  (defruled previous-quorum-p-of-advance-next
    (implies (and (previous-quorum-p systate)
                  (advance-possiblep val systate))
             (previous-quorum-p (advance-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-advance-next))

  ;; commit:

  (defruled validator-previous-quorum-p-of-commit-next
    (implies (and (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (set::in val1 (correct-addresses systate))
                  (set::in cert
                           (validator-state->dag
                            (get-validator-state val1 systate)))
                  (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (commit-possiblep val systate)
                  (addressp val))
             (validator-previous-quorum-p
              cert
              (get-validator-state val1 (commit-next val systate))))
    :enable (dag-committees-p-necc
             dag-has-committees-p-necc-bind-dag
             validator-previous-quorum-p
             validator-state->blockchain-of-commit-next
             active-committee-at-round-of-extend-blockchain-no-change
             active-committee-at-previous-round-when-at-round
             blocks-ordered-even-p-of-extend-blockchain
             certificates-ordered-even-p-of-collect-anchors
             commit-possiblep
             ordered-even-p-necc-fixing
             collect-anchors-above-last-committed-round
             last-blockchain-round-p-necc-fixing
             posp
             pos-fix
             evenp))

  (defruled previous-quorum-p-of-commit-next
    (implies (and (previous-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (commit-possiblep val systate)
                  (addressp val))
             (previous-quorum-p (commit-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-commit-next))

  ;; timeout:

  (defruled validator-previous-quorum-p-of-timeout-next
    (implies (and (validator-previous-quorum-p
                   cert
                   (get-validator-state val1 systate))
                  (timeout-possiblep val systate))
             (validator-previous-quorum-p
              cert
              (get-validator-state val1 (timeout-next val systate))))
    :enable validator-previous-quorum-p)

  (defruled previous-quorum-p-of-timeout-next
    (implies (and (previous-quorum-p systate)
                  (timeout-possiblep val systate))
             (previous-quorum-p (timeout-next val systate)))
    :enable (previous-quorum-p
             previous-quorum-p-necc
             validator-previous-quorum-p-of-timeout-next))

  ;; all events:

  (defruled previous-quorum-p-of-event-next
    (implies (and (previous-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (event-possiblep event systate))
             (previous-quorum-p (event-next event systate)))
    :enable (event-possiblep
             event-next)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection previous-quorum-p-always
  :short "The invariant holds in every state
          reachable from an initial state via a sequence of events."

  (defruled previous-quorum-p-of-events-next
    (implies (and (previous-quorum-p systate)
                  (last-blockchain-round-p systate)
                  (ordered-even-p systate)
                  (dag-committees-p systate)
                  (events-possiblep events systate))
             (and (previous-quorum-p (events-next events systate))
                  (last-blockchain-round-p (events-next events systate))
                  (ordered-even-p (events-next events systate))
                  (dag-committees-p (events-next events systate))))
    :induct t
    :enable (events-possiblep
             events-next))

  (defruled previous-quorum-p-when-reachable
    (implies (and (system-initp systate)
                  (events-possiblep events systate))
             (previous-quorum-p (events-next events systate)))))
