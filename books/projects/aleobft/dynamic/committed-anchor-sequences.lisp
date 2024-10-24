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

(include-book "anchors-of-validators-def-and-init")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ committed-anchors-sequences
  :parents (correctness)
  :short "Sequences of anchors committed by validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce an operation to collect
     all the anchors committed by a validator so far,
     and we prove properties of it."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committed-anchors ((vstate validator-statep) (all-vals address-setp))
  :guard (and (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate all-vals)))
  :returns (anchors certificate-listp)
  :short "Sequence of anchors committed by a validator."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the last committed round is 0 (i.e. there is no last committed round),
     no anchors have been committed, and we return @('nil').
     Otherwise, we obtain the last committed anchor,
     and we use @(tsee collect-all-anchors) starting from that one.
     Thus, this function gives us the list of all anchors committed so far,
     in reverse chronological order
     (i.e. the latest one is the @(tsee car) of the list)."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) nil)
       (last-anchor (last-anchor vstate all-vals)))
    (collect-all-anchors last-anchor vstate.dag vstate.blockchain all-vals))
  :guard-hints
  (("Goal" :in-theory (enable last-anchor-in-dag
                              active-committee-at-round-when-last-anchor
                              certificate->round-of-last-anchor)))

  ///

  (defruled committed-anchors-when-last-is-0
    (implies (equal (validator-state->last vstate) 0)
             (equal (committed-anchors vstate vals)
                    nil)))

  (defrule consp-of-committed-anchors-when-last-not-0
    (implies (not (equal (validator-state->last vstate) 0))
             (consp (committed-anchors vstate vals)))
    :rule-classes :type-prescription)

  (defruled car-of-committed-anchors
    (implies (and (not (equal (validator-state->last vstate) 0))
                  (last-anchor vstate vals))
             (equal (car (committed-anchors vstate vals))
                    (last-anchor vstate vals)))
    :enable car-of-collect-all-anchors))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled committed-anchors-when-init
  :short "Initially, a validator has no committed anchors."
  (implies (and (system-initp systate)
                (set::in val (correct-addresses systate)))
           (equal (committed-anchors (get-validator-state val systate)
                                     (all-addresses systate))
                  nil))
  :enable (committed-anchors
           system-initp
           system-validators-initp-necc
           validator-init))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: committed-anchors-of-next
