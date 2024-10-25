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

(include-book "operations-anchors")
(include-book "properties-dags")
(include-book "property-paths-to-voted-anchor")
(include-book "properties-anchors")

(local (include-book "arithmetic-3/top" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ properties-anchors-extension
  :parents (correctness)
  :short "Properties about extending anchor sequences."
  :long
  (xdoc::topstring
   (xdoc::p
    "We show that all the anchors in a DAG from a later anchor
     are an extension of all the anchors from an earlier anchor.
     This relies on the property,
     proved in @(see property-paths-to-voted-anchor),
     that if an anchor has at least @('f+1') votes,
     there are paths to it from all the certificates in the DAG
     at least two rounds ahead.
     Under this condition, which is expressed by @(tsee dag-all-path-to-p),
     given two anchors @('anchor') and @('anchor1'),
     the latter at a later round than the former,
     all the anchors collected starting from @('anchor1')
     are an extension of all the anchors collected starting from @('anchor').
     The reason is that there must be a path from @('anchor1') to @('anchor').
     The extra anchors are exactly the ones collected
     starting from @('anchor1') down to the round of @('anchor').")
   (xdoc::p
    "We also prove a similar property
     that involves two (possibly different) DAGs:
     the sequence of all the anchors from an anchor in the second DAG
     is an extension of
     the sequence of all the anchors from an earlier anchor in the first DAG,
     if that earlier anchor has at least @('f+1') votes.
     This relies on @(see property-paths-to-other-voted-anchor)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-anchors-to-append-of-collect-anchors
  :short "Extension theorem for @(tsee collect-anchors), for a single DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is proved by induction on
     the anchors that form the extension."))
  (implies (and (certificate-setp dag)
                (anchorp anchor dag vals)
                (dag-all-path-to-p anchor dag)
                (set::in anchor1 dag)
                (natp round)
                (evenp round)
                (evenp (certificate->round anchor1))
                (< round (certificate->round anchor1))
                (>= round (certificate->round anchor)))
           (equal (collect-anchors anchor1
                                   round
                                   0
                                   dag
                                   vals)
                  (append
                   (collect-anchors anchor1
                                    round
                                    (certificate->round anchor)
                                    dag
                                    vals)
                   (collect-anchors anchor
                                    (- (certificate->round anchor) 2)
                                    0
                                    dag
                                    vals))))
  :induct (collect-anchors anchor1
                           round
                           (certificate->round anchor)
                           dag
                           vals)
  :enable (collect-anchors
           anchorp
           append
           evenp
           certificate->round-of-path-to-author+round
           path-to-author+round-in-dag)
  :hints ('(:use (:instance dag-all-path-to-p-necc
                            (cert1 anchor1)
                            (cert anchor)))))

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
                (anchorp anchor dag vals)
                (dag-all-path-to-p anchor dag)
                (anchorp anchor1 dag vals)
                (< (certificate->round anchor)
                   (certificate->round anchor1)))
           (equal (collect-all-anchors anchor1 dag vals)
                  (append
                   (collect-anchors anchor1
                                    (- (certificate->round anchor1) 2)
                                    (certificate->round anchor)
                                    dag
                                    vals)
                   (collect-all-anchors anchor dag vals))))
  :enable (collect-all-anchors
           evenp
           anchorp)
  :use (:instance collect-anchors-to-append-of-collect-anchors
                  (round (- (certificate->round anchor1) 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled collect-all-anchors-to-append-of-collect-anchors-other
  :short "Extension theorem for @(tsee collect-all-anchors), for two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows from @(tsee collect-all-anchors-to-append-of-collect-anchors).
     The existence of the later anchor in DAG 2 hypothesized in the theorem
     leads to the existence of a path to the earlier anchor in DAG 1,
     which is not @('nil') since it satisfies @(tsee anchorp),
     and thus that earlier anchor must be also in DAG 2.
     Then we use the single-DAG theoem, applied to DAG 2,
     to show the extension.
     Finally we use the fact the the sequence of anchors from the earlier one
     is the same in the two DAGs, since they are unequivocal,
     and therefore we get the desired extension result."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (anchorp anchor1 dag1 vals)
                (anchorp anchor2 dag2 vals)
                (dag-all-path-to-p anchor1 dag2)
                (< (certificate->round anchor1)
                   (certificate->round anchor2)))
           (equal (collect-all-anchors anchor2 dag2 vals)
                  (append
                   (collect-anchors anchor2
                                    (- (certificate->round anchor2) 2)
                                    (certificate->round anchor1)
                                    dag2
                                    vals)
                   (collect-all-anchors anchor1 dag1 vals))))
  :enable (anchorp
           evenp)
  :use ((:instance collect-all-anchors-to-append-of-collect-anchors
                   (dag dag2)
                   (anchor anchor1)
                   (anchor1 anchor2))
        (:instance dag-all-path-to-p-in-dag
                   (dag dag2)
                   (cert anchor1)
                   (cert1 anchor2))
        (:instance collect-all-anchors-of-unequivocal-dags
                   (last-anchor anchor1))))
