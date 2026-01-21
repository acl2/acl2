; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT")

(include-book "elections")
(include-book "dags")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ anchors
  :parents (transitions)
  :short "Anchors."
  :long
  (xdoc::topstring
   (xdoc::p
    "An anchor is a certificate in a DAG
     that is authored by the leader for the round of the certificate.")
   (xdoc::p
    "Here we define operations related to anchors."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define collect-anchors ((current-anchor certificatep)
                         (previous-round natp)
                         (last-committed-round natp)
                         (dag certificate-setp)
                         (blockchain block-listp))
  :guard (and (evenp previous-round)
              (> (certificate->round current-anchor) previous-round)
              (or (zp previous-round)
                  (active-committee-at-round previous-round blockchain)))
  :returns (anchors certificate-listp)
  :short "Collect all the anchor certificates to commit."
  :long
  (xdoc::topstring
   (xdoc::p
    "The starting point is an anchor, @('current-anchor')
     and an even round, @('previous-round'), that precedes the anchor.
     The recursion terminates when @('previous-round')
     reaches the last committed round:
     we return a singleton list with the current anchor.
     The last committed round is passed as input @('last-committed-round').
     If @('previous-round') is larger than @('last-committed-round'),
     we find the leader at @('previous-round'),
     and we use @(tsee path-to-author+round) to find the anchor, if any,
     at @('previous-round') reachable from the current anchor.
     If there is no such reachable previous anchor,
     including the possibility that
     there is no leader because the committee is empty
     (although this never happens, due to invariants proved elsewhere),
     we recursively examine the even round
     just before @('previous-round'),
     with the same @('current-anchor');
     in the recursion, we will be looking for longer paths,
     from the same @('current-anchor') to a round further behind.
     If there is an anchor at @('previous-round'),
     it becomes the new @('current-anchor'),
     and we recursively examine its previous even round,
     but since we changed @('current-anchor'),
     in the recursion DAG paths will be from the new @('current-anchor').
     The recursive call will return a list of anchors
     that includes the anchor passed as first argument.
     thus, when that anchor changes (i.e. when the previous anchor is found),
     we add the old @('current-anchor') to the list.
     The resulting list of anchors is in inverse chronological order:
     the leftmost anchor is the newest one (i.e. greatest round number);
     the rightmost anchor is the oldest one (i.e. smallest round number).")
   (xdoc::p
    "Since @('previous-round') eventually reaches @('last-committed-round')
     (at the end of the recursion),
     which is a natural number (i.e. a round number or 0),
     the @('previous-round') input of this ACL2 function
     is also a natural number (i.e. a round number or 0).")
   (xdoc::p
    "In order to calculate the leader at @('previous-round'),
     as it may also change during the recursion,
     we need to know the active committee at that round.
     So we pass the blockchain so far as an input to this function,
     and we require in the guard that the active committee
     is known at @('previous-round'),
     which implies that it is also known at smaller rounds.
     Note that the @('blockchain') input does not change in the recursion:
     it is simply the current blockchain,
     which this operation is not extending;
     this operation is just collecting the anchors
     with which the blockchain is (elsewhere) extended.
     It is an invariant, proved elsewhere,
     that @('last-committed-round') is in fact the round of the latest block
     (or 0 if the blockchain is empty).")
   (xdoc::p
    "The returned list of anchors has even round numbers,
     if @('current-anchor') has an even round number
     and if @('previous-round') is even."))
  (b* (((unless (and (mbt (and (or (zp previous-round)
                                   (active-committee-at-round previous-round
                                                              blockchain))
                               t))
                     (> (nfix previous-round)
                        (nfix last-committed-round))))
        (list (certificate-fix current-anchor)))
       (commtt (active-committee-at-round previous-round blockchain))
       ((unless (committee-nonemptyp commtt))
        (collect-anchors current-anchor
                         (- (nfix previous-round) 2)
                         last-committed-round
                         dag
                         blockchain))
       (previous-leader (leader-at-round previous-round commtt))
       (previous-anchor? (path-to-author+round current-anchor
                                               previous-leader
                                               previous-round
                                               dag))
       ((unless previous-anchor?)
        (collect-anchors current-anchor
                         (- (nfix previous-round) 2)
                         last-committed-round
                         dag
                         blockchain)))
    (cons (certificate-fix current-anchor)
          (collect-anchors previous-anchor?
                           (- (nfix previous-round) 2)
                           last-committed-round
                           dag
                           blockchain)))
  :measure (nfix previous-round)
  :prepwork ((local (in-theory (enable nfix))))
  :hints (("Goal" :in-theory (enable o-p o-finp o<)))
  :guard-hints
  (("Goal"
    :in-theory (enable evenp
                       active-committee-at-previous2-round-when-at-round)))
  :hooks (:fix)

  ///

  (defret car-of-collect-anchors
    (equal (car anchors)
           (certificate-fix current-anchor))
    :hints (("Goal" :induct t)))
  (in-theory (disable car-of-collect-anchors))

  (defret cert-list-evenp-of-collect-anchors
    (cert-list-evenp anchors)
    :hyp (and (evenp (certificate->round current-anchor))
              (evenp previous-round))
    :hints (("Goal" :induct t :in-theory (enable cert-list-evenp evenp))))

  (defret cert-list-orderedp-of-collect-anchors
    (cert-list-orderedp anchors)
    :hyp (< previous-round
            (certificate->round current-anchor))
    :hints (("Goal"
             :induct t
             :in-theory (enable cert-list-orderedp
                                car-of-collect-anchors
                                evenp))))
  (in-theory (disable cert-list-orderedp-of-collect-anchors))

  (defret collect-anchors-above-last-committed-round
    (> (certificate->round (car (last anchors)))
       (nfix last-committed-round))
    :hyp (> (certificate->round current-anchor)
            (nfix last-committed-round))
    :rule-classes
    ((:linear :trigger-terms ((certificate->round (car (last anchors))))))
    :hints (("Goal"
             :induct t
             :in-theory (enable last))))
  (in-theory (disable collect-anchors-above-last-committed-round)))
