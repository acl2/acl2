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

(include-book "anchors")
(include-book "initialization")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-def-and-init
  :parents (correctness)
  :short "Last anchor committed by a validator:
          definition and initial result."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an operation, and theorems about it,
     to obtain the last anchor committed by a validator.")
   (xdoc::p
    "We prove theorems expressing the initial result of this operation.")
   (xdoc::p
    "Elsewhere, we prove how the events change the result.
     We separate that because it needs theorems
     that depend on the definition of the operation."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define last-anchor ((vstate validator-statep) (all-vals address-setp))
  :returns (anchor? certificate-optionp)
  :short "Last committed anchor in a validator state."
  :long
  (xdoc::topstring
   (xdoc::p
    "A validator state includes
     a component with the latest committed round number
     (or 0 if no rounds have been committed yet).
     We return the certificate at that round
     authored by the leader of that round,
     if such a certificate is in the DAG;
     if the certificate is absent, we return @('nil').
     If no round has been committed yet, we also return @('nil').
     The validator must be able to calculate
     the active committee for the last committed round,
     in order to calculate the leader;
     we return @('nil') if the validator cannot calculate that committee."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) nil)
       (commtt (active-committee-at-round vstate.last
                                          vstate.blockchain
                                          all-vals))
       ((unless commtt) nil)
       (leader (leader-at-round vstate.last commtt)))
    (certificate-with-author+round leader vstate.last vstate.dag))
  :hooks (:fix)

  ///

  (defruled last-not-0-when-last-anchor
    (implies (last-anchor vstate all-vals)
             (not (equal (validator-state->last vstate) 0))))

  (defruled certificate->author-of-last-anchor
    (implies (last-anchor vstate all-vals)
             (equal (certificate->author (last-anchor vstate all-vals))
                    (b* ((commtt (active-committee-at-round
                                  (validator-state->last vstate)
                                  (validator-state->blockchain vstate)
                                  all-vals)))
                      (leader-at-round (validator-state->last vstate) commtt))))
    :enable certificate->author-of-certificate-with-author+round)

  (defruled certificate->round-of-last-anchor
    (implies (last-anchor vstate all-vals)
             (equal (certificate->round (last-anchor vstate all-vals))
                    (validator-state->last vstate)))
    :enable certificate->round-of-certificate-with-author+round)

  (defruled last-anchor-in-dag
    (implies (last-anchor vstate all-vals)
             (set::in (last-anchor vstate all-vals)
                      (validator-state->dag vstate)))
    :enable certificate-with-author+round-element)

  (defruled active-committee-at-round-when-last-anchor
    (implies (last-anchor vstate all-vals)
             (active-committee-at-round (validator-state->last vstate)
                                        (validator-state->blockchain vstate)
                                        all-vals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled last-anchor-when-init
  :short "Initially, a validator has no last committed anchor."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (last-anchor (get-validator-state val systate)
                               (all-addresses systate))
                  nil))
  :enable (last-anchor
           system-initp
           system-validators-initp-necc
           validator-init))
