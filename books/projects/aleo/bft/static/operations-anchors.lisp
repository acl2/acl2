; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "operations-leaders")
(include-book "operations-blockchain")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-anchors
  :parents (operations-additional)
  :short "Operations for anchors."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(see operations-leaders),
     if there is a certificate at an even round
     authored by the leader of that round,
     the certificate is an anchor.
     Here we introduce some operations related to anchors."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define last-anchor ((vstate validator-statep) (vals address-setp))
  :guard (and (not (set::emptyp vals))
              (evenp (validator-state->last vstate)))
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
     If no round has been committed yet, we also return @('nil')."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) nil)
       (leader (leader-at-round vstate.last vals)))
    (cert-with-author+round leader vstate.last vstate.dag))

  ///

  (defruled certificate->author-of-last-anchor
    (implies (last-anchor vstate vals)
             (equal (certificate->author (last-anchor vstate vals))
                    (leader-at-round (validator-state->last vstate) vals)))
    :enable certificate->author-of-cert-with-author+round)

  (defruled certificate->round-of-last-anchor
    (implies (last-anchor vstate vals)
             (equal (certificate->round (last-anchor vstate vals))
                    (validator-state->last vstate)))
    :enable certificate->round-of-cert-with-author+round)

  (defruled last-anchor-in-dag
    (implies (last-anchor vstate vals)
             (set::in (last-anchor vstate vals) (validator-state->dag vstate)))
    :enable cert-with-author+round-element))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define anchorp ((anchor certificatep)
                 (dag certificate-setp)
                 (vals address-setp))
  :guard (not (set::emptyp vals))
  :returns (yes/no booleanp)
  :short "Check if a certificate is an anchor in a DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "Besides the certificate and the DAG,
     we also pass the set of validator addresses to this predicate.
     That set is needed to calculate the leader
     at the round of the certificate,
     to check whether the address of the certificate
     is the leader of that round.
     We also check that the certificate is in the DAG.")
   (xdoc::p
    "This predicate does not require,
     either in the guard or as a check in the body,
     that the round is even, although anchors are only at even rounds.
     So this predicate is perhaps slightly looser than it should be,
     but it is not wrong, as it can be used for even rounds only as needed."))
  (and (set::in anchor dag)
       (evenp (certificate->round anchor))
       (equal (certificate->author anchor)
              (leader-at-round (certificate->round anchor) vals)))

  ///

  (defruled not-anchorp-of-nil
    (not (anchorp nil dag vals)))

  (defruled anchorp-of-last-anchor
    (implies (and (last-anchor vstate vals)
                  (evenp (validator-state->last vstate)))
             (anchorp (last-anchor vstate vals)
                      (validator-state->dag vstate)
                      vals))
    :enable (anchorp
             cert-with-author+round-element
             certificate->author-of-last-anchor
             certificate->round-of-last-anchor
             last-anchor-in-dag)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define collect-all-anchors ((last-anchor certificatep)
                             (dag certificate-setp)
                             (vals address-setp))
  :guard (and (set::in last-anchor dag)
              (evenp (certificate->round last-anchor))
              (not (set::emptyp vals)))
  :returns (all-anchors certificate-listp)
  :short "Collect all the anchors in a DAG,
          starting from a given anchor."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(tsee collect-anchors)
     that does not stop at the last committed rounds,
     but instead goes all the way to the start of the DAG.")
   (xdoc::p
    "The input @('last-anchor') is a certificate
     (not necessarily an anchor,
     although normally it is when this function is called)
     at an even round.
     We collect that anchor, and all the ones at preceding even rounds
     recursively reachable from this certificate;
     see @(tsee collect-anchors) for details of the process."))
  (collect-anchors last-anchor
                   (- (certificate->round last-anchor) 2)
                   0
                   dag
                   vals)
  :guard-hints (("Goal" :in-theory (enable evenp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define committed-anchors ((vstate validator-statep) (vals address-setp))
  :guard (and (not (set::emptyp vals))
              (evenp (validator-state->last vstate))
              (or (equal (validator-state->last vstate) 0)
                  (last-anchor vstate vals)))
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
     (i.e. the last one come first in the list)."))
  (b* (((validator-state vstate) vstate)
       ((when (equal vstate.last 0)) nil)
       (last-anchor (last-anchor vstate vals)))
    (collect-all-anchors last-anchor vstate.dag vals))
  :guard-hints (("Goal" :in-theory (enable certificate->round-of-last-anchor
                                           last-anchor-in-dag)))

  ///

  (defruled committed-anchors-when-last-is-0
    (implies (equal (validator-state->last vstate) 0)
             (equal (committed-anchors vstate vals)
                    nil)))

  (defruled consp-of-committed-anchors-when-last-not-0
    (implies (not (equal (validator-state->last vstate) 0))
             (consp (committed-anchors vstate vals)))
    :rule-classes :type-prescription)

  (defruled car-of-committed-anchors
    (implies (and (not (equal (validator-state->last vstate) 0))
                  (last-anchor vstate vals))
             (equal (car (committed-anchors vstate vals))
                    (last-anchor vstate vals)))
    :enable (collect-all-anchors
             car-of-collect-anchors)))
