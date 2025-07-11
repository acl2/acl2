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

(include-book "certificates")
(include-book "dags")
(include-book "committees")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ successor-predecessor-intersection
  :parents (correctness)
  :short "Intersection of successors and predecessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the second key intersection argument
     for the correctness of AleoBFT,
     besides "
    (xdoc::seetopic "quorum-intersection" "quorum intersection")
    ". However, this second argument is very different:
     it has nothing to do with correct and faulty validators;
     it only has to do with paths in DAGs.
     When an anchor @($A$) at a round @($r$)
     has enough voting stake from the successors at round @($r+1$),
     then if there is a certificate @($C$) at round @($r+2$)
     there must be a certificate @($B$) at round @($r+1$)
     that is both a successor (i.e. voter) of @($A$)
     and a predecessor of @($C$).")
   (xdoc::p
    "This applies, as stated, to each single validator DAG.
     But it also applies, with a slight modification,
     to the DAGs of two different validators.
     In this case.
     @($A$) is in DAG 1,
     @($C$) is in DAG 2,
     and, instead of a single @($B$),
     there are a @($B_1$) in DAG 1
     and a @($B_2$) in DAG 2,
     such that @($B_1$) and @($B_2$) contain the same proposal,
     but possibly different endorsers.
     This matches the notion of non-equivocation
     expressed by @(tsee cert-sets-prop-unequivp):
     as explained there, AleoBFT guarantees
     the non-equivocation of proposals in DAGs,
     but not necessarily of whole certificates.")
   (xdoc::p
    "The case of a single validator DAG is a special one,
     where @($B_1 = B_2$) and DAGs 1 and 2 are the same.
     Here we state our theorems with respect to two DAGs,
     which may or may not be equal.")
   (xdoc::p
    "We introduce a function that,
     given the two DAGs,
     and given @($A$) in DAG 1 and @($C$) in DAG 2,
     returns @($B_1$) and @($B_2$) if they can be found (otherwise @('nil')).
     We prove that, under suitable conditions,
     this function returns two certificates with the expected properties.")
   (xdoc::p
    "Here we talk about successors and predecessors,
     not specifically voters and anchors,
     because the argument is more general.")
   (xdoc::p
    "We still use the term `intersection' for this argument because,
     although @($B_1$) and @($B_2$) may differ
     (i.e. it is not a single @($B$) as in a true intersection),
     it is still somewhat of an intersection.
     One could think of the common proposal in @($B_1$) and @($B_2$)
     as being in the intersection of the proposals of the DAGs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled not-empty-successor-predecessor-author-intersection
  :short "Non-empty intersection of successor and predecessor authors."
  :long
  (xdoc::topstring
   (xdoc::p
    "In this theorem @('n') and @('f') are
     the @($n$) and @($f$) mentioned in @(tsee max-faulty-for-total).
     With reference to @(see successor-predecessor-intersection),
     here @('successor-vals') represents
     the authors of the successors of @($A$),
     while @('predecessor-vals') represents
     the authors of the predecessors of @($C$).")
   (xdoc::p
    "If (i) the total stake of successor and predecessor authors
     is bounded by @('n'),
     (ii) the total stake of the successor authors
     is more than @('f'),
     and (iii) the total stake of the predecessor authors
     is at least @('n - f'),
     then in order for the two sets to have no intersection
     their total stake would have to be more than @('n'),
     which contradicts the first hypothesis.
     So there must be at least one in the intersection."))
  (implies (and (address-setp succ-vals)
                (address-setp pred-vals)
                (<= (validators-stake (set::union succ-vals pred-vals) commtt)
                    n)
                (> (validators-stake succ-vals commtt)
                   f)
                (>= (validators-stake pred-vals commtt)
                    (- n f)))
           (not (set::emptyp (set::intersect succ-vals pred-vals))))
  :use (:instance not-emptyp-when-validators-stake-gt-0
                  (vals (set::intersect succ-vals pred-vals)))
  :enable validators-stake-of-intersect)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pick-successor+predecessor ((dag1 certificate-setp)
                                    (dag2 certificate-setp)
                                    (cert1 certificatep)
                                    (cert2 certificatep))
  :guard (and (set::in cert1 dag1)
              (set::in cert2 dag2)
              (equal (certificate->round cert2)
                     (+ 2 (certificate->round cert1))))
  :returns (mv (succ? certificate-optionp)
               (pred? certificate-optionp))
  :short "Pick a successor @($B_1$) of @($A$) in DAG 1
          and a predecessor @($B_2$) of @($C$) in DAG 2
          with the same proposal."
  :long
  (xdoc::topstring
   (xdoc::p
    "Refer to @(see successor-predecessor-intersection).")
   (xdoc::p
    "We intersect the authors of successors and predecessors.
     If the intersection is empty, we return @('nil') for both certificates.
     Otherwise, we pick a common author from the intersection,
     and we pick (if any) the certificates with that author
     and with the round between the two certificates
     (note the guard requiring @($C$) to be two rounds ahead of @($A$).")
   (xdoc::p
    "The successor @($B_1$), if non-@('nil',
     is both in the successors of @($A$) and in DAG 1.
     The predecessor @($B_2$), if non-@('nil',
     is both in the predecessors of @($C$) and in DAG 2.
     Successor and predecessor, if non-@('nil'),
     have the same author and round.
     Thus, if the two DAGs are mutually unequivocal,
     successor and predecessor have the same proposal."))
  (b* ((common-authors (set::intersect
                        (cert-set->author-set (successors cert1 dag1))
                        (cert-set->author-set (predecessors cert2 dag2)))))
    (if (set::emptyp common-authors)
        (mv nil nil)
      (b* ((common-author (set::nonemptyp-witness common-authors)))
        (mv (cert-with-author+round common-author
                                    (1+ (certificate->round cert1))
                                    dag1)
            (cert-with-author+round common-author
                                    (1- (certificate->round cert2))
                                    dag2)))))
  :guard-hints
  (("Goal" :in-theory (enable set::nonemptyp-witness-from-not-emptyp)))
  :hooks (:fix)

  ///

  (defret pick-successor-in-dag
    (implies succ?
             (set::in succ? dag1))
    :hyp (certificate-setp dag1)
    :hints (("Goal" :in-theory (enable cert-with-author+round-element))))

  (defret pick-predecessor-in-dag
    (implies pred?
             (set::in pred? dag2))
    :hyp (certificate-setp dag2)
    :hints (("Goal" :in-theory (enable cert-with-author+round-element))))

  (defret pick-successor-in-successors
    (implies succ?
             (set::in succ? (successors cert1 dag1)))
    :hyp (certificate-setp dag1)
    :hints (("Goal"
             :use ((:instance set::nonemptyp-witness-from-not-emptyp
                              (set (intersect (cert-set->author-set
                                               (successors cert1 dag1))
                                              (cert-set->author-set
                                               (predecessors cert2 dag2)))))
                   (:instance cert-with-author+round-subset-superset-same
                              (certs0 (successors cert1 dag1))
                              (certs dag1)
                              (cert (set::nonemptyp-witness
                                     (certs-with-author
                                      (set::nonemptyp-witness
                                       (intersect
                                        (cert-set->author-set
                                         (successors cert1 dag1))
                                        (cert-set->author-set
                                         (predecessors cert2 dag2))))
                                      (successors cert1 dag1))))
                              (author (set::nonemptyp-witness
                                       (intersect
                                        (cert-set->author-set
                                         (successors cert1 dag1))
                                        (cert-set->author-set
                                         (predecessors cert2 dag2)))))
                              (round (1+ (certificate->round cert1))))
                   (:instance cert-with-author+round-element
                              (certs (successors cert1 dag1))
                              (author (set::nonemptyp-witness
                                       (intersect
                                        (cert-set->author-set
                                         (successors cert1 dag1))
                                        (cert-set->author-set
                                         (predecessors cert2 dag2)))))
                              (round (1+ (certificate->round cert1)))))
             :in-theory (enable* in-of-cert-set->author-set
                                 in-of-successors))))

  (defret pick-predecessor-in-predecessors
    (implies pred?
             (set::in pred? (predecessors cert2 dag2)))
    :hyp (certificate-setp dag2)
    :hints (("Goal"
             :use ((:instance set::nonemptyp-witness-from-not-emptyp
                              (set (intersect (cert-set->author-set
                                               (successors cert1 dag1))
                                              (cert-set->author-set
                                               (predecessors cert2 dag2)))))
                   (:instance cert-with-author+round-subset-superset-same
                              (certs0 (predecessors cert2 dag2))
                              (certs dag2)
                              (cert (set::nonemptyp-witness
                                     (certs-with-author
                                      (set::nonemptyp-witness
                                       (intersect
                                        (cert-set->author-set
                                         (successors cert1 dag1))
                                        (cert-set->author-set
                                         (predecessors cert2 dag2))))
                                      (predecessors cert2 dag2))))
                              (author (set::nonemptyp-witness
                                       (intersect
                                        (cert-set->author-set
                                         (successors cert1 dag1))
                                        (cert-set->author-set
                                         (predecessors cert2 dag2)))))
                              (round (1- (certificate->round cert2))))
                   (:instance cert-with-author+round-element
                              (certs (predecessors cert2 dag2))
                              (author (set::nonemptyp-witness
                                       (intersect
                                        (cert-set->author-set
                                         (successors cert1 dag1))
                                        (cert-set->author-set
                                         (predecessors cert2 dag2)))))
                              (round (1- (certificate->round cert2)))))
             :in-theory (enable* in-of-cert-set->author-set
                                 in-of-predecessors))))

  (defret pick-successor+predecessor-same-author
    (implies (and succ? pred?)
             (equal (certificate->author succ?)
                    (certificate->author pred?))))

  (defret pick-successor+predecessor-same-round
    (implies (and succ? pred?)
             (equal (certificate->round succ?)
                    (certificate->round pred?)))
    :hyp (equal (certificate->round cert2)
                (+ 2 (certificate->round cert1))))

  (defret pick-successor+predecessor-same-proposal
    (implies (and succ? pred?)
             (equal (certificate->proposal succ?)
                    (certificate->proposal pred?)))
    :hyp (and (certificate-setp dag1)
              (certificate-setp dag2)
              (cert-sets-prop-unequivp dag1 dag2)
              (equal (certificate->round cert2)
                     (+ 2 (certificate->round cert1))))
    :hints
    (("Goal"
      :in-theory (disable pick-successor+predecessor)
      :use (:instance cert-sets-prop-unequivp-necc
                      (certs1 dag1)
                      (certs2 dag2)
                      (cert1 (mv-nth 0 (pick-successor+predecessor
                                        dag1 dag2 cert1 cert2)))
                      (cert2 (mv-nth 1 (pick-successor+predecessor
                                        dag1 dag2 cert1 cert2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pick-successor+predecessor-when-succ/pred-intersection
  :short "Conditions under which @(tsee pick-successor+predecessor)
          returns two certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given two (possibly different) unequivocal DAGs,
     a certificate @($A$) in DAG 1
     whose successors have more than
     the maximum tolerated faulty stake in a committee,
     a certificate @($C$) in DAG2
     whose predecessors have at least
     the quorum stake in the same committee,
     and @($C$) being two rounds ahead of @($A$),
     we have that @(tsee pick-predecessor-in-predecessors)
     returns two non-@('nil') certificates @($B_1$) and @($B_2$),
     whose properties are proved
     in theorems in @(tsee pick-predecessor-in-predecessors).")
   (xdoc::p
    "Before proving the main theorem,
     we prove two auxiliary theorems:
     one about @($A$) and @($B_1$) in DAG 1,
     and one about @($C$) and @($B_2$) in DAG 2."))

  (defruled cert-with-author+round-of-successor
    (implies (and (certificate-setp dag1)
                  (cert-set-unequivp dag1)
                  (set::in cert1 dag1)
                  (set::in common-author
                           (cert-set->author-set (successors cert1 dag1))))
             (cert-with-author+round common-author
                                     (1+ (certificate->round cert1))
                                     dag1))
    :enable (in-of-cert-set->author-set
             in-of-successors)
    :use (:instance cert-with-author+round-of-cert-in-unequiv-certs
                    (certs dag1)
                    (cert (set::nonemptyp-witness
                           (certs-with-author common-author
                                              (successors cert1 dag1))))))

  (defruled cert-with-author+round-of-predecessor
    (implies (and (certificate-setp dag2)
                  (cert-set-unequivp dag2)
                  (set::in cert2 dag2)
                  (set::in common-author
                           (cert-set->author-set (predecessors cert2 dag2))))
             (cert-with-author+round common-author
                                     (1- (certificate->round cert2))
                                     dag2))
    :enable (in-of-cert-set->author-set
             in-of-predecessors)
    :use (:instance cert-with-author+round-of-cert-in-unequiv-certs
                    (certs dag2)
                    (cert (set::nonemptyp-witness
                           (certs-with-author common-author
                                              (predecessors cert2 dag2))))))

  (defruled pick-successor+predecessor-when-succ/pred-intersection
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (cert-set-unequivp dag1)
                  (cert-set-unequivp dag2)
                  (set::in cert1 dag1)
                  (set::in cert2 dag2)
                  (equal (certificate->round cert2)
                         (+ 2 (certificate->round cert1)))
                  (> (validators-stake (cert-set->author-set
                                        (successors cert1 dag1))
                                       commtt)
                     (committee-max-faulty-stake commtt))
                  (> (validators-stake (cert-set->author-set
                                        (predecessors cert2 dag2))
                                       commtt)
                     (committee-quorum-stake commtt)))
             (b* (((mv succ? pred?)
                   (pick-successor+predecessor dag1 dag2 cert1 cert2)))
               (and succ?
                    pred?)))
    :enable (pick-successor+predecessor
             committee-quorum-stake
             validators-stake-upper-bound
             set::not-emptyp-to-nonemptyp
             set::nonemptyp
             cert-with-author+round-of-successor
             cert-with-author+round-of-predecessor)
    :use (:instance not-empty-successor-predecessor-author-intersection
                    (succ-vals (cert-set->author-set (successors cert1 dag1)))
                    (pred-vals (cert-set->author-set (predecessors cert2 dag2)))
                    (n (committee-total-stake commtt))
                    (f (committee-max-faulty-stake commtt)))))
