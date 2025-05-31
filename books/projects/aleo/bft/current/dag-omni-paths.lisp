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

(include-book "dags")
(include-book "successor-predecessor-intersection")

(local (include-book "std/basic/inductions" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dag-omni-paths
  :parents (correctness)
  :short "Property that certain certificates in DAGs
          are reachable from all the certificates in later rounds,
          also in different DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a core property of AleoBFT.
     Take an anchor @($A$) (or any certificate, for that matter) in a DAG,
     with more than @($f$) voting stake
     (where @($f$) is introduced in @(tsee max-faulty-for-total)),
     i.e. where the total stake of successors in the round just after @($A$)
     is more than  @($f$).
     Then if there is a(ny) certificate @($C$) two rounds after @($A$),
     its predecessors in the round just before,
     which is the same as the round just after @($A$),
     must have at least @($n-f$) total stake.
     Since there can be at most @($n$) total stake in that round
     (the same round that is both just after @($A$) and just before @($C$)),
     the intersection argument in @(see successor-predecessor-intersection)
     shows that there must be a certificate @($B$) between @($A$) and @($C$).
     That is, there is a path from @($C$) to @($A$), through @($B$).
     The above holds for every @($C$) two rounds after @($A$).
     Any certificate @($D$) in the round after @($C$)
     must have predecessors in the previous round,
     which, as argued, all have paths to @($A$),
     and therefore every @($D$) has a path to @($A$) as well.
     Thus, every certificate at least two rounds after @($A$)
     has a path to @($A$).")
   (xdoc::p
    "The above has been explained for one DAG,
     because it is easier to understand,
     but it also holds across two DAGs of possibly different validators.
     Given a certificate (anchor) @($A$) in DAG 1 at round @($r$),
     with more than @($f$) voting stake for @($A$) in DAG 1 at round @($r+1$),
     and at least @($n-f$) predecessor stake in DAG 2 at round @($r+1$),
     every certificate @($C$) in DAG 2 at round @($r+2$) or later
     has a path to @($A$), which must be also in DAG 2.
     The reason is that there must be a certificate @($B$)
     that is both in the successors of @($A$) in DAG 1
     and in the predecessors of @($C$) in DAG 2.
     In DAG 1, it has an edge to @($A$).
     Because of the backward closure of DAG 2,
     @($A$) must be in DAG 2 too, with an edge to it from @($B$).
     Since @($B$) is a predecessor of @($C$),
     there is a path from @($C$) to @($A$).
     This holds for every @($C$) in DAG 2 in round @($r+2$),
     so every @($D$) in DAG 2 at round @($r+3$)
     has a predecessor @($C$) with a path to @($A$)
     and so @($D$) has a path to @($A$) too.
     And so on for the rest of the rounds of DAG2.")
   (xdoc::p
    "Here we formulate and prove this core property, for two DAGs.
     We do not need to talk about anchors specifically,
     because @($A$) can be any certificate,
     not necessarily at an even round,
     not necessarily a leader certificate
     so long as it has more than @($f$) successors' stake."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-omni-paths-p ((cert certificatep) (dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if all the certificates
          that are at least two rounds after a given certificate
          have a path to that certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the predicate expressing the key property that we prove here,
     where @('cert') is the certificate with more than @($f$) successors' stake.
     We universally quantify over a generic certificate @('cert1')
     whose round is greater than or equal to
     two plus the round of the given certificate @('cert').
     The existence of the path is expressed by saying that
     @(tsee path-to-author+round) applied to @('cert1')
     with the author and round of @('cert') as targets
     yields exactly @('cert').")
   (xdoc::p
    "The certificate @('cert') passed as input
     is the certificate @($A$) in the discussion in @(see dag-omni-paths).")
   (xdoc::p
    "We prove that if the DAG has
     at least one certificate at least two rounds after the given one,
     then the given certificate must be in the DAG,
     because there is at least one path to it."))
  (forall (cert1)
          (implies (and (set::in cert1 dag)
                        (>= (certificate->round cert1)
                            (+ 2 (certificate->round cert))))
                   (equal (path-to-author+round cert1
                                                (certificate->author cert)
                                                (certificate->round cert)
                                                dag)
                          cert)))

  ///

  (defruled in-dag-when-dag-omni-paths-p
    (implies (and (certificate-setp dag)
                  (dag-omni-paths-p cert dag)
                  (set::in cert1 dag)
                  (>= (certificate->round cert1)
                      (+ 2 (certificate->round cert)))
                  cert)
             (set::in cert dag))
    :enable path-to-author+round-in-dag
    :disable (dag-omni-paths-p
              dag-omni-paths-p-necc)
    :use dag-omni-paths-p-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-omni-paths-round-p ((round posp)
                                   (cert certificatep)
                                   (dag certificate-setp))
  :guard (>= round (+ 2 (certificate->round cert)))
  :returns (yes/no booleanp)
  :short "Check if all the certificates at a certain round
          that is at least two rounds after a given certificate
          have a path to that certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a version of @(tsee dag-omni-paths-p)
     restricted to a given round, passed as input.
     The guard requires the given round to be
     at least two rounds after the certificate's round,
     which matches the antecedent in the universal quantification
     in the definition of @(tsee dag-omni-paths-p).")
   (xdoc::p
    "The reason why we define this predicate is that
     below we prove @(tsee dag-omni-paths-p) by induction on rounds,
     starting from two rounds just after the certificate.
     With reference to the discussion in @(see dag-omni-paths),
     @('cert') is @($A$),
     and the base case of the induction is for
     the generic certificate @($C$) two rounds after @($A$),
     while the generic certificate @($D$) is at later rounds.
     So we prove below that this predicate holds for every round,
     in the induction proof."))
  (forall (cert1)
          (implies (and (set::in cert1 dag)
                        (equal (certificate->round cert1) round))
                   (equal (path-to-author+round cert1
                                                (certificate->author cert)
                                                (certificate->round cert)
                                                dag)
                          cert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-omni-paths-rounds-p ((cert certificatep) (dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if @(tsee dag-omni-paths-rounds-p) holds for all rounds
          that are at least two rounds after the given certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This provides an alternative definition of @(tsee dag-omni-paths-p)
     as a quantification over the rounds of @(tsee dag-omni-paths-round-p),
     which is convenient for our proof by induction, as mentioned above.
     We prove that it is indeed equivalent to @(tsee dag-omni-paths-p),
     which is conceptually easy but takes a few steps
     to deal with the quantifiers."))
  (forall (round)
          (implies (and (posp round)
                        (>= round (+ 2 (certificate->round cert))))
                   (dag-omni-paths-round-p round cert dag)))

  ///

  (defruled dag-omni-paths-p-alt-def
    (equal (dag-omni-paths-p cert dag)
           (dag-omni-paths-rounds-p cert dag))
    :use (dag-all-path-to-p-alt-when-dag-all-path-to-p
          dag-all-path-to-p-when-dag-all-path-to-p-alt)

    :prep-lemmas

    ((defruled dag-omni-paths-round-p-when-dag-omni-paths-p
       (implies (and (dag-omni-paths-p cert dag)
                     (posp round)
                     (>= round (+ 2 (certificate->round cert))))
                (dag-omni-paths-round-p round cert dag))
       :enable (dag-omni-paths-round-p
                dag-omni-paths-p-necc))

     (defruled dag-all-path-to-p-alt-when-dag-all-path-to-p
       (implies (dag-omni-paths-p cert dag)
                (dag-omni-paths-rounds-p cert dag))
       :enable (dag-omni-paths-rounds-p
                dag-omni-paths-round-p-when-dag-omni-paths-p))

     (defruled dag-all-path-to-p-when-dag-all-path-to-p-alt
       (implies (dag-omni-paths-rounds-p cert dag)
                (dag-omni-paths-p cert dag))
       :use (:instance dag-omni-paths-rounds-p-necc
                       (round (certificate->round
                               (dag-omni-paths-p-witness cert dag))))
       :enable (dag-omni-paths-p
                dag-omni-paths-round-p-necc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-from-common-to-cert1-in-dag2
  :short "There is a path in @('dag2')
          from the common certificate in the intersection
          to @('cert1') in @('dag1'),
          which is also in @('dag2')."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since the common certificate is a successor of @('cert1') in @('dag1'),
     there is a path in @('dag1') from the common certificate to @('cert1').
     But since the common certificate is also in @('dag2'),
     and the two DAGs are (individually and mutually) unequivocal,
     the result of @(tsee path-to-author+round)
     applied to the common certificate (as source)
     must be the same in the two DAGs, namely @('cert1').
     So we have that @('cert1') is also in @('dag2') besides @('dag1')."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (dag-closedp dag1)
                (dag-closedp dag2)
                (set::in cert1 dag1)
                (set::in cert2 dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1)))
                (dag-has-committees-p dag1 blockchain1)
                (dag-has-committees-p dag2 blockchain2)
                (dag-in-committees-p dag1 blockchain1)
                (dag-in-committees-p dag2 blockchain2)
                (same-active-committees-p blockchain1 blockchain2)
                (dag-predecessor-quorum-p dag2 blockchain2)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert1 dag1))
                    (active-committee-at-round (1+ (certificate->round cert1))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert1))
                                               blockchain1))))
           (and (equal (path-to-author+round
                        (pick-successor/predecessor dag1 dag2 cert1 cert2)
                        (certificate->author cert1)
                        (certificate->round cert1)
                        dag2)
                       cert1)
                (set::in cert1 dag2)))
  :enable (path-from-successor
           pick-successor/predecessor-properties
           nil-not-in-certificate-set)
  :use ((:instance path-to-author+round-of-unequivocal-dags
                   (author (certificate->author cert1))
                   (round (certificate->round cert1))
                   (cert (pick-successor/predecessor dag1 dag2 cert1 cert2)))
        (:instance path-to-author+round-in-dag
                   (dag dag2)
                   (author (certificate->author cert1))
                   (round (certificate->round  cert1))
                   (cert (pick-successor/predecessor dag1 dag2 cert1 cert2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-from-cert2-to-cert1-in-dag2
  :short "There is a path in @('dag2') from @('cert2') to @('cert1')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is obtained by composing
     the path proved in @(tsee path-from-common-to-cert1-in-dag2),
     from the common certificate to @('cert1'),
     with the path from @('cert2') to the common certificate.
     The latter path exists because
     the common certificate is a predecessor of @('cert2')."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (dag-closedp dag1)
                (dag-closedp dag2)
                (set::in cert1 dag1)
                (set::in cert2 dag2)
                (equal (certificate->round cert2)
                       (+ 2 (certificate->round cert1)))
                (dag-has-committees-p dag1 blockchain1)
                (dag-has-committees-p dag2 blockchain2)
                (dag-in-committees-p dag1 blockchain1)
                (dag-in-committees-p dag2 blockchain2)
                (same-active-committees-p blockchain1 blockchain2)
                (dag-predecessor-quorum-p dag2 blockchain2)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert1 dag1))
                    (active-committee-at-round (1+ (certificate->round cert1))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert1))
                                               blockchain1))))
           (equal (path-to-author+round cert2
                                        (certificate->author cert1)
                                        (certificate->round cert1)
                                        dag2)
                  cert1))
  :use (:instance path-to-author+round-transitive
                  (cert cert2)
                  (cert1 (pick-successor/predecessor dag1 dag2 cert1 cert2))
                  (cert2 cert1)
                  (dag dag2))
  :enable (path-to-predecessor
           pick-successor/predecessor-properties
           path-from-common-to-cert1-in-dag2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-omni-paths-round-p-base-case
  :short "Base case of our proof by induction."
  :long
  (xdoc::topstring
   (xdoc::p
    "With reference to the discussion in @(see dag-omni-paths),
     we want to show that there are paths to @($A$) in round @($r$)
     from certificates in every round @($r' \\geq r+2$).
     We do that by induction on the round,
     so the base case is for a generic certificate @($C$) at round @($r+2$);
     more precisely, we prove @(tsee dag-omni-paths-round-p) for @($r+2$).
     This is an easy consequence of @(tsee path-from-cert2-to-cert1-in-dag2),
     where @('cert1') is @($A$) and @('cert2') is a generic @($C$)."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (dag-closedp dag1)
                (dag-closedp dag2)
                (set::in cert dag1)
                (dag-has-committees-p dag1 blockchain1)
                (dag-has-committees-p dag2 blockchain2)
                (dag-in-committees-p dag1 blockchain1)
                (dag-in-committees-p dag2 blockchain2)
                (same-active-committees-p blockchain1 blockchain2)
                (dag-predecessor-quorum-p dag2 blockchain2)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert dag1))
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1))))
           (dag-omni-paths-round-p (+ 2 (certificate->round cert))
                                   cert
                                   dag2))
  :enable dag-omni-paths-round-p
  :use (:instance path-from-cert2-to-cert1-in-dag2
                  (cert1 cert)
                  (cert2 (dag-omni-paths-round-p-witness
                          (+ 2 (certificate->round cert))
                          cert
                          dag2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-omni-paths-round-p-of-next-round
  :short "Preservation of @(tsee dag-omni-paths-round-p)
          from one round to the next."
  :long
  (xdoc::topstring
   (xdoc::p
    "Having proved the base case in @(tsee dag-omni-paths-round-p-base-case),
     we need to prove the step case, which is done via this theorem first.
     This theorem says that
     if every certificate in round @($r'$) has a path to @($A),
     then every certificate in round @($r'+1$) has a path to @($A$);
     here @('cert') is @($A$).
     The reason is that every certificate in round @($r'+1$)
     has a path to its predecessors,
     and each such predecessor has a path to @($A$) by the induction hypothesis
     (which is stated as an explicit hypothesis in this theorem).
     We use the transitivity of DAG paths,
     to compose the path from round @($r'+1$) to @($r'$)
     with the path from round @($r'$) to certificate @($A$).
     We need to choose a specific predecessor,
     and we pick the first one (i.e. @(tsee set::head));
     its existence is guaranteed by @(tsee dag-predecessor-quorum-p),
     and the fact that the quorum stake is always positive.")
   (xdoc::p
    "Although our proof by induction involves two DAGs,
     this theorem only involves one,
     because the induction step only involves paths in @('dag2').")
   (xdoc::p
    "Note that we use a weaker assumption on @('cert')
     than the fact that it is in the DAG,
     namely just that it is non-@('nil').
     This facilitates the final proof by induction,
     which will just have the hypothesis that @($A$) is in @('dag1'),
     but not in @('dag2') as required for this theorem to apply.
     We know that @($A$) is in @('dag2') as well
     by @(tsee path-from-cert2-to-cert1-in-dag2),
     but that theorem has hypotheses about @('cert2') (i.e. @($C$))
     which are not readily available in the proof by induction.
     Indeed, note that @($A$) is also in @('dag2')
     only if there is some certificate at round @($r+2$) or later;
     otherwise, @($A$) may not be in @('dag2') at all.
     But by using the weaker hypothesis that @('cert') is not @('nil'),
     we can easily relieve this hypothesis from the fact that
     the anchor is in @('dag1'), as available in the proof by induciton,
     which implies that it is not @('nil')."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-closedp dag)
                (dag-predecessor-quorum-p dag blockchain)
                cert ; weaker than (set::in cert dag)
                (posp round)
                (dag-omni-paths-round-p round cert dag))
           (dag-omni-paths-round-p (1+ round) cert dag))
  :expand (dag-omni-paths-round-p (1+ round) cert dag)
  :use ((:instance path-to-author+round-transitive
                   (cert (dag-omni-paths-round-p-witness
                          (+ 1 round) cert dag))
                   (cert1 (set::head
                           (predecessors
                            (dag-omni-paths-round-p-witness
                             (+ 1 round) cert dag)
                            dag)))
                   (cert2 cert))
        (:instance path-to-head-of-predecessors
                   (cert (dag-omni-paths-round-p-witness
                          (+ 1 round) cert dag)))
        (:instance dag-omni-paths-round-p-necc
                   (cert1 (set::head
                           (predecessors
                            (dag-omni-paths-round-p-witness
                             (+ 1 round) cert dag)
                            dag))))
        (:instance path-to-author+round-in-dag
                   (cert (set::head
                          (predecessors
                           (dag-omni-paths-round-p-witness
                            (+ 1 round) cert dag)
                           dag)))
                   (author (certificate->author cert))
                   (round (certificate->round cert))))
  :enable (not-emptyp-predecessors-when-dag-predecessor-quorum-p
           head-of-predecessors-in-predecessors
           round-of-head-of-predecessors
           head-of-predecessors-in-dag
           fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-omni-paths-round-p-step-case
  :short "Step case of our proof by induction."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple consequence of
     @(tsee dag-omni-paths-round-p-of-next-round),
     but it is formulated in a way usable in the proof by induction.
     Instead of rounds @($r'$) and @($r'+1$),
     this theorem is formulated in terms of rounds
     @($a + 2 + d$) and @($a + 2 + d + 1$),
     where @($a$) is the round of @($A$)
     and @($d$) is a generic ``delta'' from @($a+2$).
     Note that this has the same weaker hypothesis on @($A$),
     namely that is not @('nil'), as opposed to being in the DAG."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-closedp dag)
                (dag-predecessor-quorum-p dag blockchain)
                cert ; weaker than (set::in cert dag)
                (natp round-delta)
                (dag-omni-paths-round-p (+ round-delta
                                           (+ 2 (certificate->round cert)))
                                        cert
                                        dag))
           (dag-omni-paths-round-p (+ (1+ round-delta)
                                      (+ 2 (certificate->round cert)))
                                   cert
                                   dag))
  :use (:instance dag-omni-paths-round-p-of-next-round
                  (round (+ round-delta
                            (certificate->round cert)
                            2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-omni-paths-round-p-of-round-delta
  :short "Induction proof."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove by induction that @(tsee dag-omni-paths-round-p) holds
     for every round of the form @($a + 2 + d$),
     where @($a$) is the round of @($A$),
     and @($d$) is a generic ``delta'' from @($a + 2$).
     We use the previously proved base and step cases;
     it should be clear why the step case
     was formulated in terms of @($a + 2 + d$) and @($a + 2 + d + 1$)."))
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
                (dag-predecessor-quorum-p dag2 blockchain2)
                (set::in cert dag1)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert dag1))
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1)))
                (natp round-delta))
           (dag-omni-paths-round-p (+ round-delta
                                      (+ 2 (certificate->round cert)))
                                   cert
                                   dag2))
  :induct (acl2::dec-induct round-delta)
  :enable nil-not-in-certificate-set
  :hints ('(:use (dag-omni-paths-round-p-base-case
                  (:instance dag-omni-paths-round-p-step-case
                             (round-delta (1- round-delta))
                             (blockchain blockchain2)
                             (dag dag2))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-omni-paths-round-p-holds
  :short "Proof that @(tsee dag-omni-paths-round-p) holds
          for every round @($r' \\geq a+2$)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is just a reformulation of
     @(tsee dag-omni-paths-round-p-of-round-delta),
     with a generic round @($r'$), constrained to be @($a+2$) or more.
     This is an appropriate form for our final proof,
     in @(tsee dag-omni-paths-p-holds)."))
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
                (dag-predecessor-quorum-p dag2 blockchain2)
                (set::in cert dag1)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert dag1))
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1)))
                (natp round)
                (>= round
                    (+ 2 (certificate->round cert))))
           (dag-omni-paths-round-p round cert dag2))
  :use (:instance dag-omni-paths-round-p-of-round-delta
                  (round-delta (- round (+ 2 (certificate->round cert)))))
  :enable (fix natp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled dag-omni-paths-p-holds
  :short "Proof that @(tsee dag-omni-paths-p) holds."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the proof of our desired property.
     We rewrite @(tsee dag-omni-paths-p)
     to its alternative definition @(tsee dag-omni-paths-rounds-p),
     we expand the latter,
     and we use @(tsee dag-omni-paths-round-p-holds)
     to prove that @(tsee dag-omni-paths-round-p)
     holds on the generic witness."))
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
                (dag-predecessor-quorum-p dag2 blockchain2)
                (set::in cert dag1)
                (> (committee-members-stake
                    (cert-set->author-set (successors cert dag1))
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1))
                   (committee-max-faulty-stake
                    (active-committee-at-round (1+ (certificate->round cert))
                                               blockchain1))))
           (dag-omni-paths-p cert dag2))
  :enable (dag-omni-paths-p-alt-def
           dag-omni-paths-rounds-p)
  :use (:instance dag-omni-paths-round-p-holds
                  (round (dag-omni-paths-rounds-p-witness cert dag2))))
