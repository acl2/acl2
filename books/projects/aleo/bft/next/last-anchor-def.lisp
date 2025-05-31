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

(include-book "validator-states")
(include-book "elections")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ last-anchor-def
  :parents (correctness)
  :short "Last anchor committed by a validator: definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an operation to obtain
     the last anchor committed by a validator.
     The operation returns @('nil') if
     the validator has not committed any anchors yet."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define last-anchor ((vstate validator-statep))
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
     and the committee must be non-empty,
     in order to calculate the leader;
     we return @('nil') if
     the validator cannot calculate that committee
     or that committee is empty."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) nil)
       (commtt (active-committee-at-round vstate.last vstate.blockchain))
       ((unless commtt) nil)
       ((unless (committee-nonemptyp commtt)) nil)
       (leader (leader-at-round vstate.last commtt)))
    (cert-with-author+round leader vstate.last vstate.dag))
  :hooks (:fix)

  ///

  (defruled last-not-0-when-last-anchor
    (implies (last-anchor vstate)
             (not (equal (validator-state->last vstate) 0))))

  (defruled active-committee-at-round-when-last-anchor
    (implies (last-anchor vstate)
             (active-committee-at-round (validator-state->last vstate)
                                        (validator-state->blockchain vstate))))

  (defruled certificate->author-of-last-anchor
    (implies (last-anchor vstate)
             (equal (certificate->author (last-anchor vstate))
                    (b* ((commtt (active-committee-at-round
                                  (validator-state->last vstate)
                                  (validator-state->blockchain vstate))))
                      (leader-at-round (validator-state->last vstate)
                                       commtt)))))

  (defruled certificate->round-of-last-anchor
    (implies (last-anchor vstate)
             (equal (certificate->round (last-anchor vstate))
                    (validator-state->last vstate))))

  (defruled last-anchor-in-dag
    (implies (last-anchor vstate)
             (set::in (last-anchor vstate)
                      (validator-state->dag vstate)))
    :enable cert-with-author+round-element))
