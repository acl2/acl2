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
                         (blockchain block-listp)
                         (all-vals address-setp))
  :guard (and (evenp previous-round)
              (> (certificate->round current-anchor) previous-round)
              (or (zp previous-round)
                  (active-committee-at-round previous-round
                                             blockchain
                                             all-vals)))
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
     The last committed round is passed as input @('last-committed-round');
     it is initially 0, when there is no committed round yet.
     If @('previous-round') is larger than the @('last-committed-round'),
     we find the leader at @('previous-round'),
     and we use @(tsee path-to-author+round) to find the anchor, if any,
     at @('previous-round') reachable from the current anchor.
     If there is no such reachable previous anchor,
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
     Note that this @('blockchain') input does not change in the recursion:
     it is simply the current blockchain,
     which this operation is not extending;
     this operation is just collecting the anchors
     with which the blockchain is (elsewhere) extended.
     It should be an invariant (not captured here)
     that @('last-committed-round') is in fact the round of the latest block
     (or 0 if the blockchain is empty);
     we plan to prove this invariant, as done for
     the model of AleoBFT with static committees.")
   (xdoc::p
    "The role of the @('all-vals') input is
     explained in @(tsee update-committee-with-transaction).")
   (xdoc::p
    "The returned list of anchors is never empty,
     and it always starts with (i.e. its @(tsee car) is)
     the @('current-anchor') input,
     as we prove below.")
   (xdoc::p
    "we also prove that the returned list of anchors has even,
     strictly increasing (right to left) round numbers,
     under suitable assumptions on some of the inputs.")
   (xdoc::p
    "We also show that the rounds of the returned anchors
     are all above the last committed round,
     provided that the round of the input anchor is.
     More precisely, we say that the lowest-numbered anchor round
     (i.e. the @(tsee car) of @(tsee last), i.e. the rightmost one)
     is above the last committed round.
     This assumption is satisfied when this function is called.
     Note that, since we also proved that rounds are strictly increasing,
     proving that the rightmost anchor has round above the last committed one
     implies that all the other anchors do as well;
     but in any case we need the theorem in this form,
     with @(tsee car) of @(tsee last),
     so it can be used to relieve the hypothesis
     in a theorem about @(tsee extend-blockchain)."))
  (b* (((unless (and (mbt (and (natp previous-round)
                               (evenp previous-round)
                               (natp last-committed-round)
                               (or (zp previous-round)
                                   (active-committee-at-round previous-round
                                                              blockchain
                                                              all-vals))
                               t))
                     (> previous-round last-committed-round)))
        (list (certificate-fix current-anchor)))
       (commtt (active-committee-at-round previous-round
                                          blockchain
                                          all-vals))
       (previous-leader (leader-at-round previous-round commtt))
       (previous-anchor? (path-to-author+round current-anchor
                                               previous-leader
                                               previous-round
                                               dag)))
    (if previous-anchor?
        (cons (certificate-fix current-anchor)
              (collect-anchors previous-anchor?
                               (- previous-round 2)
                               last-committed-round
                               dag
                               blockchain
                               all-vals))
      (collect-anchors current-anchor
                       (- previous-round 2)
                       last-committed-round
                       dag
                       blockchain
                       all-vals)))
  :measure (nfix previous-round)
  :hints (("Goal" :in-theory (enable o-p o-finp o< nfix)))
  :guard-hints
  (("Goal"
    :in-theory (enable evenp
                       active-committee-at-earlier-round-when-at-later-round
                       certificate->round-of-path-to-author+round)))

  ///

  (more-returns
   (anchors consp :rule-classes :type-prescription))

  (defret car-of-collect-anchors
    (equal (car anchors)
           (certificate-fix current-anchor))
    :hints (("Goal" :induct t)))
  (in-theory (disable car-of-collect-anchors))

  (defret certificates-ordered-even-p-of-collect-anchors
    (certificates-ordered-even-p anchors)
    :hyp (and (evenp (certificate->round current-anchor))
              (evenp previous-round)
              (< previous-round
                 (certificate->round current-anchor)))
    :hints (("Goal"
             :induct t
             :in-theory (enable certificates-ordered-even-p
                                car-of-collect-anchors
                                certificate->round-of-path-to-author+round))))
  (in-theory (disable certificates-ordered-even-p-of-collect-anchors))

  (defret collect-anchors-above-last-committed-round
    (> (certificate->round (car (last anchors)))
       last-committed-round)
    :hyp (> (certificate->round current-anchor)
            last-committed-round)
    :hints (("Goal"
             :induct t
             :in-theory (enable last
                                certificate->round-of-path-to-author+round))))
  (in-theory (disable collect-anchors-above-last-committed-round)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define collect-all-anchors ((last-anchor certificatep)
                             (dag certificate-setp)
                             (blockchain block-listp)
                             (all-vals address-setp))
  :guard (and (set::in last-anchor dag)
              (evenp (certificate->round last-anchor))
              (active-committee-at-round (certificate->round last-anchor)
                                         blockchain
                                         all-vals))
  :returns (all-anchors certificate-listp)
  :short "Collect all the anchors in a DAG, starting from a given anchor."
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
     see @(tsee collect-anchors) for details of the process.")
   (xdoc::p
    "The guard requires that the active committee can be calculated
     for the round of @('last-anchor').
     This is a little more than needed
     to satisfy the guard of @(tsee collect-anchors)
     (which just need the committee for two rounds before that one),
     but it is slightly simpler,
     and in fact satisfied when we call @('collect-all-anchors')."))
  (collect-anchors last-anchor
                   (- (certificate->round last-anchor) 2)
                   0
                   dag
                   blockchain
                   all-vals)
  :guard-hints
  (("Goal"
    :in-theory (enable evenp
                       active-committee-at-earlier-round-when-at-later-round)))

  ///

  (defret car-of-collect-all-anchors
    (equal (car all-anchors)
           (certificate-fix last-anchor))
    :hints (("Goal" :in-theory (enable car-of-collect-anchors))))

  (in-theory (disable car-of-collect-all-anchors)))
