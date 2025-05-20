; AleoBFT Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-ARXIV")

(include-book "dag-omni-paths")
(include-book "anchors")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ anchors-extension
  :parents (correctness)
  :short "Extension of anchor sequences."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that all the anchors in a DAG from a later anchor
     are an extension of all the anchors from an earlier anchor.
     This relies on the property, proved in @(see dag-omni-paths),
     that if an anchor has more than @($f$) voting stake,
     there are paths to it from all the certificates
     at least two rounds ahead in the same or different DAG.
     Under this condition, which is expressed by @(tsee dag-omni-paths-p),
     given two anchors @('anchor') and @('anchor1'),
     the latter at a later round than the former,
     all the anchors collected starting from @('anchor1')
     are an extension of all the anchors collected starting from @('anchor').
     The reason is that there must be a path from @('anchor1') to @('anchor').
     The extra anchors are exactly the ones collected
     starting from @('anchor1') down to the round of @('anchor')."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-anchors-to-append-of-collect-anchors
  :short "Extension theorem for @(tsee collect-anchors), for a single DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by induction on
     the anchors that form the extension.
     We have two anchors, @('anchor') and @('anchor1'),
     with the latter coming strictly after the former.
     In order to prove this theorem by induction,
     we formulate it over a generic round @('round')
     between @('anchor') (inclusive) and @('anchor1') (exclusive),
     which matches the @('previous-round') formal of @(tsee collect-anchors),
     and is in fact its measured subset that is involved in the induction.")
   (xdoc::p
    "In the base case, @('round') is the round of @('anchor'),
     and the equality to prove reduces to:")
   (xdoc::codeblock
    "(equal (cons anchor1"
    "             (collect-anchors anchor"
    "                              (- (certificate->round anchor) 2)"
    "                              0 dag blockchain))"
    "       (append (list anchor)"
    "               (collect-anchors anchor"
    "                                (- (certificate->round anchor) 2)"
    "                                0 dag blockchain)))")
   (xdoc::p
    "The @(tsee cons) on the left side arises
     thanks to the @(tsee dag-omni-paths-p) hypothesis,
     which tells us that there is a path from @('anchor1') to @('anchor').
     The @('(list anchor)') on the right side
     is the result of the call of @(tsee collect-anchors)
     which is the first argument of @(tsee append).
     The second argument of @(tsee append) is unchanged.
     Clearly, the two sides are equal.")
   (xdoc::p
    "In the step case, @('round') is later than @('anchor').
     Both calls of @(tsee collect-anchors) on @('round')
     expand to terms involving the same recursive calls,
     and the induction hypothesis ensures equality."))
  (implies (and (certificate-setp dag)
                (dag-has-committees-p dag blockchain)
                (dag-in-committees-p dag blockchain)
                (set::in anchor dag)
                (evenp (certificate->round anchor))
                (equal (certificate->author anchor)
                       (leader-at-round (certificate->round anchor)
                                        (active-committee-at-round
                                         (certificate->round anchor)
                                         blockchain)))
                (dag-omni-paths-p anchor dag)
                (set::in anchor1 dag)
                (evenp (certificate->round anchor1))
                (natp round)
                (evenp round)
                (< round (certificate->round anchor1))
                (>= round (certificate->round anchor)))
           (equal (collect-anchors anchor1
                                   round
                                   0
                                   dag
                                   blockchain)
                  (append
                   (collect-anchors anchor1
                                    round
                                    (certificate->round anchor)
                                    dag
                                    blockchain)
                   (collect-anchors anchor
                                    (- (certificate->round anchor) 2)
                                    0
                                    dag
                                    blockchain))))
  :induct (collect-anchors anchor1
                           round
                           (certificate->round anchor)
                           dag
                           blockchain)
  :enable (collect-anchors
           active-committee-at-earlier-round-when-at-later-round
           path-to-author+round-in-dag
           committee-nonemptyp-when-dag-in-committees-p
           append
           evenp)
  :hints ('(:use ((:instance dag-omni-paths-p-necc
                             (cert1 anchor1)
                             (cert anchor))
                  (:instance dag-has-committees-p-necc
                             (cert anchor1))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-all-anchors-to-append-of-collect-anchors
  :short "Extension theorem for @(tsee collect-all-anchors), for a single DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from @(tsee collect-anchors-to-append-of-collect-anchors),
     since @(tsee collect-all-anchors) is essentially
     a wrapper of @(tsee collect-anchors)."))
  (implies (and (certificate-setp dag)
                (dag-has-committees-p dag blockchain)
                (dag-in-committees-p dag blockchain)
                (set::in anchor dag)
                (evenp (certificate->round anchor))
                (equal (certificate->author anchor)
                       (leader-at-round (certificate->round anchor)
                                        (active-committee-at-round
                                         (certificate->round anchor)
                                         blockchain)))
                (dag-omni-paths-p anchor dag)
                (set::in anchor1 dag)
                (evenp (certificate->round anchor1))
                (< (certificate->round anchor)
                   (certificate->round anchor1)))
           (equal (collect-all-anchors anchor1 dag blockchain)
                  (append
                   (collect-anchors anchor1
                                    (- (certificate->round anchor1) 2)
                                    (certificate->round anchor)
                                    dag
                                    blockchain)
                   (collect-all-anchors anchor dag blockchain))))
  :enable (collect-all-anchors
           evenp)
  :use (:instance collect-anchors-to-append-of-collect-anchors
                  (round (- (certificate->round anchor1) 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-all-anchors-to-append-of-collect-anchors-dags
  :short "Extension theorem for @(tsee collect-all-anchors), for two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from @(tsee collect-all-anchors-to-append-of-collect-anchors).
     The existence of the later anchor in DAG 2 hypothesized in the theorem
     leads to the existence of a path to the earlier anchor in DAG 1,
     which is not @('nil') since it is a certificate in DAG 1,
     and thus that earlier anchor must be also in DAG 2.
     Then we use the single-DAG theorem, applied to DAG 2,
     to show the extension.
     Finally we use the fact the the sequence of anchors from the earlier one
     is the same in the two DAGs, since they are unequivocal,
     and therefore we get the desired extension result."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (dag-closedp dag1)
                (dag-closedp dag2)
                (dag-has-committees-p dag1 blockchain1)
                (dag-has-committees-p dag2 blockchain2)
                (dag-in-committees-p dag1 blockchain1)
                (dag-in-committees-p dag2 blockchain2)
                (same-active-committees-p blockchain1 blockchain2)
                (set::in anchor1 dag1)
                (evenp (certificate->round anchor1))
                (equal (certificate->author anchor1)
                       (leader-at-round (certificate->round anchor1)
                                        (active-committee-at-round
                                         (certificate->round anchor1)
                                         blockchain1)))
                (dag-omni-paths-p anchor1 dag2)
                (set::in anchor2 dag2)
                (evenp (certificate->round anchor2))
                (< (certificate->round anchor1)
                   (certificate->round anchor2)))
           (equal (collect-all-anchors anchor2 dag2 blockchain2)
                  (append
                   (collect-anchors anchor2
                                    (- (certificate->round anchor2) 2)
                                    (certificate->round anchor1)
                                    dag2
                                    blockchain2)
                   (collect-all-anchors anchor1 dag1 blockchain1))))
  :enable (evenp
           active-committee-at-earlier-round-when-at-later-round
           same-active-committees-p-necc
           dag-has-committees-p-necc)
  :use ((:instance collect-all-anchors-to-append-of-collect-anchors
                   (dag dag2)
                   (blockchain blockchain2)
                   (anchor anchor1)
                   (anchor1 anchor2))
        (:instance in-dag-when-dag-omni-paths-p
                   (dag dag2)
                   (cert anchor1)
                   (cert1 anchor2))
        (:instance collect-all-anchors-of-unequivocal-dags
                   (last-anchor anchor1))))
