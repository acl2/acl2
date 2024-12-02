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
     The last committed round is passed as input @('last-committed-round');
     it is initially 0, when there is no committed round yet.
     If @('previous-round') is larger than the @('last-committed-round'),
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
    "The returned list of anchors is never empty,
     and it always starts with (i.e. its @(tsee car) is)
     the @('current-anchor') input,
     as we prove below.")
   (xdoc::p
    "The returned list of anchors has even,
     strictly increasing (right to left) round numbers,
     under suitable assumptions on some of the inputs.")
   (xdoc::p
    "The returned list of anchors consists of certificates
     that are all in the DAG and are connected by paths;
     see @(tsee certificates-dag-paths-p).")
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
                                                              blockchain))
                               t))
                     (> previous-round last-committed-round)))
        (list (certificate-fix current-anchor)))
       (commtt (active-committee-at-round previous-round blockchain))
       ((unless (committee-nonemptyp commtt))
        (collect-anchors current-anchor
                         (- previous-round 2)
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
                         (- previous-round 2)
                         last-committed-round
                         dag
                         blockchain)))
    (cons (certificate-fix current-anchor)
          (collect-anchors previous-anchor?
                           (- previous-round 2)
                           last-committed-round
                           dag
                           blockchain)))
  :measure (nfix previous-round)
  :hints (("Goal" :in-theory (enable o-p o-finp o< nfix)))
  :guard-hints
  (("Goal"
    :in-theory (enable evenp
                       active-committee-at-previous2-round-when-at-round
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
                                car-of-collect-anchors))))
  (in-theory (disable certificates-ordered-even-p-of-collect-anchors))

  (defret certificates-dag-paths-p-of-collect-anchors
    (certificates-dag-paths-p anchors dag)
    :hyp (and (certificate-setp dag)
              (set::in current-anchor dag)
              (< previous-round
                 (certificate->round current-anchor)))
    :hints (("Goal"
             :induct t
             :in-theory (enable collect-anchors
                                certificates-dag-paths-p
                                car-of-collect-anchors))))
  (in-theory (disable certificates-dag-paths-p-of-collect-anchors))

  (defret collect-anchors-above-last-committed-round
    (> (certificate->round (car (last anchors)))
       last-committed-round)
    :hyp (> (certificate->round current-anchor)
            last-committed-round)
    :hints (("Goal"
             :induct t
             :in-theory (enable last))))
  (in-theory (disable collect-anchors-above-last-committed-round)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection collect-anchors-in-unequivocal-closed-dags
  :short "Some theorems about @(tsee collect-anchors)
          applied on unequivocal, backward-closed DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     the anchors collected, starting from an anchor,
     from a backward-closed subset of an unequivocal DAG
     are the same in the superset.
     The anchor collection in question is the one
     expressed by the @(tsee collect-anchors) operation,
     which collects anchors starting from a given one
     down to a given round (or 0 for all rounds).
     If the starting anchor is in the subset,
     it must also be in the superset,
     and collecting the anchors in the superset
     yields the same result as collecting the anchors in the subset.
     That is, the collection of anchors is stable under DAG growth.
     This builds on the stability property of paths under DAG growth,
     expressed by the theorem @('path-to-author+round-of-unequivocal-superdag')
     in @(see paths-in-unequivocal-closed-dags);
     the collection of anchors is based on the paths,
     both present and absent paths,
     which that theorem shows to be stable under DAG growth.
     The proof is fairly simple, by induction on @(tsee collect-anchors).")
   (xdoc::p
    "The second theorem says that
     the anchors collected, starting from a common anchor,
     from two backward-closed, (individually and mutually) unequivocal DAGs
     are the same in the two DAGs.
     The proof is also by induction on @(tsee collect-anchors):
     although there are two calls with different arguments,
     the measured subset (i.e. @('previous-round')) is the same in both calls.
     We need more hypotheses (which are implied by already proved invariants),
     to ensure that the two blockchains result in the same committees,
     and thus in the same leaders at each round of interest."))

  (defruled collect-anchors-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::in current-anchor dag0))
             (equal (collect-anchors current-anchor
                                     previous-round
                                     last-committed-round
                                     dag
                                     blockchain)
                    (collect-anchors current-anchor
                                     previous-round
                                     last-committed-round
                                     dag0
                                     blockchain)))
    :induct t
    :enable (collect-anchors
             path-to-author+round-of-unequivocal-superdag))

  (defruled collect-anchors-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (dag-has-committees-p dag1 blockchain1)
                  (dag-has-committees-p dag2 blockchain2)
                  (same-active-committees-p blockchain1 blockchain2)
                  (set::in current-anchor dag1)
                  (set::in current-anchor dag2)
                  (< previous-round (certificate->round current-anchor)))
             (equal (collect-anchors current-anchor
                                     previous-round
                                     last-committed-round
                                     dag1
                                     blockchain1)
                    (collect-anchors current-anchor
                                     previous-round
                                     last-committed-round
                                     dag2
                                     blockchain2)))
    :induct t
    :enable (collect-anchors
             dag-has-committees-p-necc
             path-to-author+round-of-unequivocal-dags)
    :hints ('(:use ((:instance
                     active-committee-at-earlier-round-when-at-later-round
                     (later (certificate->round current-anchor))
                     (earlier previous-round)
                     (blocks blockchain1))
                    (:instance
                     active-committee-at-earlier-round-when-at-later-round
                     (later (certificate->round current-anchor))
                     (earlier previous-round)
                     (blocks blockchain2))
                    (:instance
                     same-active-committees-p-necc
                     (blocks1 blockchain1)
                     (blocks2 blockchain2)
                     (round previous-round))
                    (:instance
                     path-to-author+round-in-dag
                     (cert current-anchor)
                     (author (leader-at-round
                              previous-round
                              (active-committee-at-round
                               previous-round blockchain1)))
                     (round previous-round)
                     (dag dag1))
                    (:instance
                     path-to-author+round-in-dag
                     (cert current-anchor)
                     (author (leader-at-round
                              previous-round
                              (active-committee-at-round
                               previous-round blockchain1)))
                     (round previous-round)
                     (dag dag2)))
              :expand ((collect-anchors current-anchor
                                        previous-round
                                        last-committed-round
                                        dag2
                                        blockchain2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define collect-all-anchors ((last-anchor certificatep)
                             (dag certificate-setp)
                             (blockchain block-listp))
  :guard (and (set::in last-anchor dag)
              (evenp (certificate->round last-anchor))
              (active-committee-at-round (certificate->round last-anchor)
                                         blockchain))
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
     and in fact satisfied when we call @('collect-all-anchors').")
   (xdoc::p
    "The returned list of anchors satisfies @(tsee certificates-dag-paths-p)."))
  (collect-anchors last-anchor
                   (- (certificate->round last-anchor) 2)
                   0
                   dag
                   blockchain)
  :guard-hints
  (("Goal"
    :in-theory
    (enable evenp
            active-committee-at-previous2-round-when-at-round)))

  ///

  (defret car-of-collect-all-anchors
    (equal (car all-anchors)
           (certificate-fix last-anchor))
    :hints (("Goal" :in-theory (enable car-of-collect-anchors))))
  (in-theory (disable car-of-collect-all-anchors))

  (defret certificates-dag-paths-p-of-collect-all-anchors
    (certificates-dag-paths-p all-anchors dag)
    :hyp (and (certificate-setp dag)
              (set::in last-anchor dag))
    :hints
    (("Goal" :in-theory (enable certificates-dag-paths-p-of-collect-anchors))))
  (in-theory (disable certificates-dag-paths-p-of-collect-all-anchors)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection collect-all-anchors-in-unequivocal-closed-dags
  :short "Some theorems about @(tsee collect-all-anchors)
          applied on unequivocal, backward-closed DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     all the anchors collected, starting from an anchor,
     from a backward-closed subset of an unequivocal DAG
     are the same in the superset.
     This is a simple consequence of the analogous theorem
     about @(tsee collect-anchors).")
   (xdoc::p
    "The second theorem says that
     all the anchors collected, starting from a common anchor,
     from two backward-closed, (individually and mutually) unequivocal DAGs
     are the same in the two DAGS.
     This is a simple consequence of the analogous theorem
     about @(tsee collect-anchors)."))

  (defruled collect-all-anchors-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::in last-anchor dag0))
             (equal (collect-all-anchors last-anchor dag blockchain)
                    (collect-all-anchors last-anchor dag0 blockchain)))
    :enable (collect-all-anchors
             collect-anchors-of-unequivocal-superdag))

  (defruled collect-all-anchors-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (dag-has-committees-p dag1 blockchain1)
                  (dag-has-committees-p dag2 blockchain2)
                  (same-active-committees-p blockchain1 blockchain2)
                  (set::in last-anchor dag1)
                  (set::in last-anchor dag2))
             (equal (collect-all-anchors last-anchor dag1 blockchain1)
                    (collect-all-anchors last-anchor dag2 blockchain2)))
    :enable (collect-all-anchors
             collect-anchors-of-unequivocal-dags)))
