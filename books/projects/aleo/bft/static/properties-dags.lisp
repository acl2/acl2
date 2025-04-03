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

(include-book "operations-dags")
(include-book "operations-dags-additional")
(include-book "operations-voting")
(include-book "properties-certificate-retrieval")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ properties-dags
  :parents (correctness)
  :short "Some properties of the operations on DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some of these come in two forms,
     analogous to the ones described in @(see properties-certificate-retrieval):
     one form about the consistency of the growing DAG of a single validator,
     and one form about the consistency across DAGs of different validators.
     In fact, the proofs of these theorems about DAGs
     make use of those theorems about certificate retrieval.")
   (xdoc::p
    "Besides the ones mentioned just above,
     there are also other properties proved here,
     which do not come in pairs like that."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection dag-previous-in-dag-p-of-intersect
  :short "Intersecting two unequivocal backward-closed DAGs
          yields a backward-closed DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "If a certificate is in both DAGs,
     because of the backward closure of the DAGs,
     its precedecessors are also in both DAGs,
     and therefore in the intersection."))

  (defruled certificate-previous-in-dag-p-of-intersect
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-previous-in-dag-p cert dag1)
                  (certificate-previous-in-dag-p cert dag2))
             (certificate-previous-in-dag-p cert (set::intersect dag1 dag2)))
    :enable (certificate-previous-in-dag-p
             set::expensive-rules
             posp
             certs-with-round-of-intersect)
    :prep-lemmas
    ((defrule lemma
       (implies (and (certificate-setp dag1)
                     (certificate-setp dag2)
                     (certificate-sets-unequivocalp dag1 dag2)
                     (set::in author
                              (cert-set->author-set
                               (certs-with-round round dag1)))
                     (set::in author
                              (cert-set->author-set
                               (certs-with-round round dag2)))
                     (posp round))
                (set::in author
                         (cert-set->author-set
                          (set::intersect
                           (certs-with-round round dag1)
                           (certs-with-round round dag2)))))
       :enable (cert-with-author+round-element
                cert-with-author+round-when-author-in-round
                in-of-certs-with-round)
       :disable certificate->author-in-cert-set->author-set
       :use ((:instance certificate-sets-unequivocalp-necc
                        (cert1 (cert-with-author+round
                                author round dag1))
                        (cert2 (cert-with-author+round
                                author round dag2))
                        (certs1 dag1)
                        (certs2 dag2))
             (:instance certificate->author-in-cert-set->author-set
                        (cert (cert-with-author+round
                               author round dag1))
                        (certs (set::intersect
                                (certs-with-round round dag1)
                                (certs-with-round round dag2))))))))

  (defruled dag-previous-in-dag-p-of-intersect
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (dag-previous-in-dag-p dag1)
                  (dag-previous-in-dag-p dag2))
             (dag-previous-in-dag-p (set::intersect dag1 dag2)))
    :expand (dag-previous-in-dag-p (set::intersect dag1 dag2))
    :enable (dag-previous-in-dag-p-necc
             certificate-previous-in-dag-p-of-intersect)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled previous-certificates-of-unequivocal-dag-superset
  :short "The predecessor cerfificates of a certificate
          in a backward-closed subset of a DAG of unequivocal certificates
          are the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This was alluded to in
     @(tsee certs-with-authors+round-of-unequivocal-superset),
     which is in fact used in the proof.
     The theorem here has @(tsee dag-previous-in-dag-p) as hypothesis,
     which is why it is under @(see properties-dags)
     and not @(see properties-certificate-retrieval).")
   (xdoc::p
    "Note that the unequivocation of the superset
     implies the unequivocation of the subset,
     but the backward closure of the subset
     does not imply the backward closure of the superset.
     The latter is not needed, in fact.
     The backward closure of the subset establishes the hypothesis of
     @(tsee certs-with-authors+round-of-unequivocal-superset)
     that the previous authors of the certificate
     are all in the round just before the certificate.")
   (xdoc::p
    "This theorem says that, as the DAG of a validator grows,
     the predecessors of existing certificates do not change.")
   (xdoc::p
    "See @(tsee previous-certificates-of-unequivocal-dags)
     for an analogous theorem involving two mutually unequivocal DAGs."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (set::subset dag1 dag2)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (set::in cert dag1)
                (or (not (equal (certificate->round cert) 1))
                    (set::emptyp (certificate->previous cert))))
           (equal (certs-with-authors+round
                   (certificate->previous cert)
                   (1- (certificate->round cert))
                   dag2)
                  (certs-with-authors+round
                   (certificate->previous cert)
                   (1- (certificate->round cert))
                   dag1)))
  :enable certificate-previous-in-dag-p
  :use ((:instance dag-previous-in-dag-p-necc
                   (dag dag1)
                   (cert cert))
        (:instance certs-with-authors+round-of-unequivocal-superset
                   (certs1 dag1)
                   (certs2 dag2)
                   (authors (certificate->previous cert))
                   (round (1- (certificate->round cert))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled previous-certificates-of-unequivocal-dags
  :short "The predecessor certificates of a common certificate
          of two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to
     @(tsee previous-certificates-of-unequivocal-dag-superset),
     but for two DAGs of different validators
     instead of a growing DAG of a single validator.")
   (xdoc::p
    "This was alluded to in
     @(tsee certs-with-authors+round-of-unequivocal-sets)
     as the main application of that theorem.
     However, we actually prove this without using that theorem:
     we use @(tsee previous-certificates-of-unequivocal-dag-superset) twice,
     where the subset is the intersection of the two DAGs both times,
     while the superset is either one or the other DAG.
     This uses the fact that backward closure
     is closed under intersection, proved earlier.")
   (xdoc::p
    "We could probably prove this theorem by directly using
     @(tsee certs-with-authors+round-of-unequivocal-sets)
     and avoiding the @(tsee certificate-set-unequivocalp) hypothesis.
     But those hypothesis will be satisfied,
     so there is no loss of generality in having them."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (set::subset dag1 dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::in cert dag1)
                (set::in cert dag2)
                (or (not (equal (certificate->round cert) 1))
                    (set::emptyp (certificate->previous cert))))
           (equal (certs-with-authors+round
                   (certificate->previous cert)
                   (1- (certificate->round cert))
                   dag1)
                  (certs-with-authors+round
                   (certificate->previous cert)
                   (1- (certificate->round cert))
                   dag2)))
  :use ((:instance previous-certificates-of-unequivocal-dag-superset
                   (dag1 (set::intersect dag1 dag2))
                   (dag2 dag1))
        (:instance previous-certificates-of-unequivocal-dag-superset
                   (dag1 (set::intersect dag1 dag2))
                   (dag2 dag2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection path-to-author+round-of-unequivocal-dag-superset
  :short "The paths from a certificate
          in a backward-closed subset of a DAG of unequivocal certificates
          are the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "As proved in @(tsee previous-certificates-of-unequivocal-dag-superset),
     the predecessors are the same in the superset,
     because of the backward closure.
     The same argument can be applied to the predecessors of the predecessors,
     and that covers all paths.")
   (xdoc::p
    "That is the case not just for paths that reach certificates,
     but also for paths that do not reach cdertificates.
     If the smaller DAG has no path from a certificate
     to a certain author and round,
     neither does the larger DAG.
     If it did, the backward closure would imply that
     the smaller DAG must have a path too.")
   (xdoc::p
    "This theorem tells us that, as the DAG of a validator grows,
     paths from existing certificates (both present and absent paths)
     are unaffected by the DAG's growth.
     New certificates with new paths from these new certificates
     may be certainly added as the DAG grows,
     but those do not affect certificates that are already there.")
   (xdoc::p
    "See @(tsee path-to-author+round-of-unequivocal-dags)
     for an analogous theorem relevant to DAGs of different validators."))

  (local
   (defthm-path-to-author+round-flag
     (defthm path-to-author+round-of-unequivocal-dag-superset
       (implies (and (certificate-setp dag)
                     (certificate-setp dag2)
                     (set::subset dag dag2)
                     (certificate-set-unequivocalp dag2)
                     (dag-previous-in-dag-p dag)
                     (set::in cert dag))
                (equal (path-to-author+round cert author round dag2)
                       (path-to-author+round cert author round dag)))
       :flag path-to-author+round)
     (defthm path-to-author+round-set-of-unequivocal-dag-superset
       (implies (and (certificate-setp dag)
                     (certificate-setp dag2)
                     (set::subset dag dag2)
                     (certificate-set-unequivocalp dag2)
                     (dag-previous-in-dag-p dag)
                     (set::subset certs dag))
                (equal (path-to-author+round-set certs author round dag2)
                       (path-to-author+round-set certs author round dag)))
       :flag path-to-author+round-set)
     :hints (("Goal"
              :in-theory (enable* path-to-author+round
                                  path-to-author+round-set
                                  set::expensive-rules
                                  certs-with-authors+round-subset))
             (cond
              ((acl2::occur-lst '(acl2::flag-is 'path-to-author+round) clause)
               '(:use (:instance
                       previous-certificates-of-unequivocal-dag-superset
                       (dag1 dag)
                       (dag2 dag2))))))))

  (defruled path-to-author+round-of-unequivocal-dag-superset
    (implies (and (certificate-setp dag)
                  (certificate-setp dag2)
                  (set::subset dag dag2)
                  (certificate-set-unequivocalp dag2)
                  (dag-previous-in-dag-p dag)
                  (set::in cert dag))
             (equal (path-to-author+round cert author round dag2)
                    (path-to-author+round cert author round dag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-author+round-of-unequivocal-dags
  :short "The paths from a common certificate
          of two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to
     @(tsee path-to-author+round-of-unequivocal-dag-superset),
     but for two DAGs of different validators
     instead of a growing DAG of a single validator.")
   (xdoc::p
    "Similarly to @(tsee previous-certificates-of-unequivocal-dags),
     we prove this from @(tsee path-to-author+round-of-unequivocal-dag-superset)
     using the closure of backward closure under intersection."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::in cert dag1)
                (set::in cert dag2))
           (equal (path-to-author+round cert author round dag1)
                  (path-to-author+round cert author round dag2)))
  :use ((:instance path-to-author+round-of-unequivocal-dag-superset
                   (dag (set::intersect dag1 dag2))
                   (dag2 dag1))
        (:instance path-to-author+round-of-unequivocal-dag-superset
                   (dag (set::intersect dag1 dag2))
                   (dag2 dag2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certificate-causal-history-of-unequivocal-dag-superset
  :short "The causal history of a certificate
          in a backward-closed subset of an unequivocal DAG
          is the same in the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "This builds on @(tsee path-to-author+round-of-unequivocal-dag-superset),
     since causal histories are defined in terms of paths.")
   (xdoc::p
    "This theorem says that causal histories are ``stable''
     as DAGs of validators grow.
     New certificates, with their own causal histories,
     may be added as the DAG grows,
     but without affecting histories of certificates already there.")
   (xdoc::p
    "This is an important property,
     because causal histories determine the certificates
     whose transactions are put into blocks
     (when anchors are committed).
     If the causal history of a certificate could change,
     the time at which a block is committed could result in
     different histories and thus transactions being committed.
     Instead, thanks to this theorem, we know that
     once a certificate is added to the DAG, with its history,
     that history never changes.
     Therefore, it does not matter when that certificate is committed:
     when it is committed (if it is committed),
     its causal history will be always the same.")
   (xdoc::p
    "See @(tsee certificate-causal-history-of-unequivocal-dags)
     for an analogous theorem about DAGs in different validators."))

  (local
   (defthm-certificate-causal-history-flag
     (defthm certificate-causal-history-of-unequivocal-dag-superset
       (implies (and (certificate-setp dag)
                     (certificate-setp dag2)
                     (set::subset dag dag2)
                     (certificate-set-unequivocalp dag2)
                     (dag-previous-in-dag-p dag)
                     (set::in cert dag))
                (equal (certificate-causal-history cert dag2)
                       (certificate-causal-history cert dag)))
       :flag certificate-causal-history)
     (defthm certificate-set-causal-history-of-unequivocal-dag-superset
       (implies (and (certificate-setp dag)
                     (certificate-setp dag2)
                     (set::subset dag dag2)
                     (certificate-set-unequivocalp dag2)
                     (dag-previous-in-dag-p dag)
                     (set::subset certs dag))
                (equal (certificate-set-causal-history certs dag2)
                       (certificate-set-causal-history certs dag)))
       :flag certificate-set-causal-history)
     :hints
     (("Goal" :in-theory (enable* certificate-causal-history
                                  certificate-set-causal-history
                                  set::expensive-rules
                                  certs-with-authors+round-subset
                                  emptyp-of-certificate-set-fix))
      (cond
       ((acl2::occur-lst '(acl2::flag-is 'certificate-causal-history) clause)
        '(:expand ((certificate-causal-history cert dag2)))))
      (cond
       ((acl2::occur-lst '(acl2::flag-is 'certificate-causal-history) clause)
        '(:use (:instance
                previous-certificates-of-unequivocal-dag-superset
                (dag1 dag)
                (dag2 dag2))))))))

  (defruled certificate-causal-history-of-unequivocal-dag-superset
    (implies (and (certificate-setp dag)
                  (certificate-setp dag2)
                  (set::subset dag dag2)
                  (certificate-set-unequivocalp dag2)
                  (dag-previous-in-dag-p dag)
                  (set::in cert dag))
             (equal (certificate-causal-history cert dag2)
                    (certificate-causal-history cert dag)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-causal-history-of-unequivocal-dags
  :short "The causal histories of a common certificate
          of two backward-closed unequivocal and mutually unequivocal DAGs
          are the same in the two DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to
     @(tsee certificate-causal-history-of-unequivocal-dag-superset),
     but for DAGs of different validators
     instead of the growing DAG of a single validator.")
   (xdoc::p
    "This is an important property for consistency of blockchains
     across different validators.
     If two validators had different causal histories for the same certificate,
     they could commit different transactions to their blockchains.
     This theorem rules out that situation."))
  (implies (and (certificate-setp dag1)
                (certificate-setp dag2)
                (certificate-sets-unequivocalp dag1 dag2)
                (certificate-set-unequivocalp dag1)
                (certificate-set-unequivocalp dag2)
                (dag-previous-in-dag-p dag1)
                (dag-previous-in-dag-p dag2)
                (set::in cert dag1)
                (set::in cert dag2))
           (equal (certificate-causal-history cert dag1)
                  (certificate-causal-history cert dag2)))
  :use ((:instance certificate-causal-history-of-unequivocal-dag-superset
                   (dag (set::intersect dag1 dag2))
                   (dag2 dag1))
        (:instance certificate-causal-history-of-unequivocal-dag-superset
                   (dag (set::intersect dag1 dag2))
                   (dag2 dag2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-author+round-to-cert-with-author+round
  :short "If a certificate in an unequivocal DAG
          has a path to a certain author and round,
          the path ends up at the certificate retrieved
          via that author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a consequence of non-equivocation.
     There can be at most one certiticate per author and round,
     so the certificate returned by the path operation
     must be the same as returned by the retrieval operation."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (addressp author)
                (posp round)
                (path-to-author+round cert author round dag))
           (equal (path-to-author+round cert author round dag)
                  (cert-with-author+round author round dag)))
  :enable (path-to-author+round-in-dag
           certificate->author-of-path-to-author+round
           certificate->round-of-path-to-author+round)
  :use (:instance cert-with-author+round-of-element-when-unequivocal
                  (certs dag)
                  (cert (path-to-author+round cert author round dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cert-with-author+round-when-path-to-author+round
  :short "If there is a path from a certificate in an unequivocal DAG
          then retrieving a certificate with that author and round
          results in a certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple consequence of, and is closely related to,
     @(tsee path-to-author+round-to-cert-with-author+round),
     but it is convenient to have this kind of rewrite rule available
     (which we keep disabled by default, as many others)."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (addressp author)
                (posp round)
                (path-to-author+round cert author round dag))
           (cert-with-author+round author round dag))
  :use path-to-author+round-to-cert-with-author+round)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection path-to-author+round-transitive
  :short "Transitivity of DAG paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is a path from @('cert') to @('cert1'),
     and a there is a path from @('cert1') to @('cert2'),
     then there is a path from @('cert') and @('cert2').
     The property is quite intuitive,
     but note that we have the hypothesis that the DAG is unequivocal.
     If the DAG were not unequivocal,
     paths to the same author and round from different certificates
     could potentially return different certificates."))

  (local

   (defthm-path-to-author+round-flag

     (defthm path-to-author+round-transitive-lemma
       (implies (and (certificate-setp dag)
                     (certificate-set-unequivocalp dag)
                     (set::in cert dag)
                     (set::in cert1 dag)
                     (set::in cert2 dag)
                     (equal author (certificate->author cert1))
                     (equal round (certificate->round cert1))
                     (equal (path-to-author+round cert
                                                  (certificate->author cert1)
                                                  (certificate->round cert1)
                                                  dag)
                            cert1)
                     (equal (path-to-author+round cert1
                                                  (certificate->author cert2)
                                                  (certificate->round cert2)
                                                  dag)
                            cert2))
                (equal (path-to-author+round cert
                                             (certificate->author cert2)
                                             (certificate->round cert2)
                                             dag)
                       cert2))
       :flag path-to-author+round)

     (defthm path-to-author+round-set-transitive-lemma
       (implies (and (certificate-setp dag)
                     (certificate-set-unequivocalp dag)
                     (set::subset certs dag)
                     (set::in cert1 dag)
                     (set::in cert2 dag)
                     (equal author (certificate->author cert1))
                     (equal round (certificate->round cert1))
                     (equal (path-to-author+round-set certs
                                                      (certificate->author cert1)
                                                      (certificate->round cert1)
                                                      dag)
                            cert1)
                     (equal (path-to-author+round cert1
                                                  (certificate->author cert2)
                                                  (certificate->round cert2)
                                                  dag)
                            cert2))
                (equal (path-to-author+round-set certs
                                                 (certificate->author cert2)
                                                 (certificate->round cert2)
                                                 dag)
                       cert2))
       :flag path-to-author+round-set)

     :hints
     (("Goal"
       :in-theory
       (enable*
        path-to-author+round
        path-to-author+round-set
        path-to-author+round-to-cert-with-author+round
        cert-with-author+round-of-element-when-unequivocal
        set::expensive-rules
        nil-not-in-certificate-set
        certs-with-authors+round-subset
        path-to-author+round-round-lte
        element-of-certificate-set-not-nil))
      '(:expand (path-to-author+round-set certs
                                          (certificate->author cert2)
                                          (certificate->round cert2)
                                          dag)))))

  (defruled path-to-author+round-transitive
    (implies (and (certificate-setp dag)
                  (certificate-set-unequivocalp dag)
                  (set::in cert dag)
                  (set::in cert1 dag)
                  (set::in cert2 dag)
                  (equal (path-to-author+round cert
                                               (certificate->author cert1)
                                               (certificate->round cert1)
                                               dag)
                         cert1)
                  (equal (path-to-author+round cert1
                                               (certificate->author cert2)
                                               (certificate->round cert2)
                                               dag)
                         cert2))
             (equal (path-to-author+round cert
                                          (certificate->author cert2)
                                          (certificate->round cert2)
                                          dag)
                    cert2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-author+round-set-to-path-to-author+round
  :short "If a certificate has a path to an author and round,
          then any set including the certificate
          has a path to that author and round,
          and it results in the same certificate,
          assuming the DAG is unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee path-to-author+round-set)
     is the mutually recursive companion of @(tsee path-to-author+round).
     It is defined by going through every element in the set,
     and calling @(tsee path-to-author+round) on each element.
     Thus, if @(tsee path-to-author+round) returns some certificate
     when called on @('cert'),
     if we put @('cert') in a set @('certs')
     and call @(tsee path-to-author+round-set),
     we must certainly reach a certificate,
     which must be the same because of non-equivocation."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (certificate-setp certs)
                (set::subset certs dag)
                (set::in cert certs)
                (path-to-author+round cert author round dag))
           (equal (path-to-author+round-set certs author round dag)
                  (path-to-author+round cert author round dag)))
  :enable (set::expensive-rules
           certificate->author-of-path-to-author+round
           certificate->author-of-path-to-author+round-set
           certificate->round-of-path-to-author+round
           certificate->round-of-path-to-author+round-set
           path-to-author+round-in-dag
           path-to-author+round-set-in-dag)
  :use (path-to-author+round-set-when-path-to-author+round-of-element
        (:instance certificate-set-unequivocalp-necc
                   (cert1 (path-to-author+round-set certs author round dag))
                   (cert2 (path-to-author+round cert author round dag))
                   (certs dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-previous
  :short "In an unequivocal DAG,
          there is always a path between a certificate
          and each of its predecessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This should be very intuitive,
     since paths arise precisely from the edges of the DAG.")
   (xdoc::p
    "Here @('cert1') is a certificate
     and @('cert') is one of its predecessors,
     as characterized by being in the immediately preceding round
     and by being authored by one of the authors referenced in @('cert1').")
   (xdoc::p
    "We use @(tsee path-to-author+round-set-to-path-to-author+round)
     to prove this theorem,
     because when @(tsee path-to-author+round) is opened,
     it exposes @(tsee path-to-author+round-set).
     We also need @('path-to-author+round-of-self'),
     applied to the certificate in the set of predecessors."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (set::in cert1 dag)
                (equal (certificate->round cert1)
                       (1+ (certificate->round cert)))
                (set::in (certificate->author cert)
                         (certificate->previous cert1)))
           (equal (path-to-author+round cert1
                                        (certificate->author cert)
                                        (certificate->round cert)
                                        dag)
                  cert))
  :use (:instance path-to-author+round-set-to-path-to-author+round
                  (certs (certs-with-authors+round
                          (certificate->previous cert1)
                          (+ -1 (certificate->round cert1))
                          dag))
                  (author (certificate->author cert))
                  (round (certificate->round cert)))
  :enable (path-to-author+round
           path-to-author+round-of-self
           nil-not-in-certificate-set
           certs-with-authors+round-subset
           in-of-certs-with-authors+round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-from-incoming
  :short "There is a path to a certificate
          from each of its incoming certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is also intuitively obvious,
     since @(tsee incoming) is based on the DAG edges,
     which define the paths.")
   (xdoc::p
    "We use the @(tsee path-to-previous) theorem to prove this,
     unsurprisingly."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (set::in cert1 (incoming cert dag)))
           (equal (path-to-author+round cert1
                                        (certificate->author cert)
                                        (certificate->round cert)
                                        dag)
                  cert))
  :enable (incoming
           path-to-previous
           in-of-certs-with-round)
  :use (:instance incoming-loop-previous-and-member
                  (cert cert1)
                  (certs (certs-with-round
                          (+ 1 (certificate->round cert))
                          dag))
                  (prev (certificate->author cert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-outgoing
  :short "There is a path from a certificate
          to each of its outgoing certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is also intuitively obvious,
     since @(tsee outgoing) is based on the DAG edges,
     which define the paths.")
   (xdoc::p
    "We use the @(tsee path-to-previous) theorem to prove this,
     unsurprisingly."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert1 dag)
                (set::in cert (outgoing cert1 dag)))
           (equal (path-to-author+round cert1
                                        (certificate->author cert)
                                        (certificate->round cert)
                                        dag)
                  cert))
  :enable (outgoing
           path-to-previous
           in-of-certs-with-authors+round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-outgoing-quorum
  :short "In a backward-closed unequivocal DAG
          whose certificates have a given number of precedessors,
          the number of outgoing certificates is equal to that number."
  :long
  (xdoc::topstring
   (xdoc::p
    "With the due exception for the first round,
     where there are no predecessors.")
   (xdoc::p
    "This is fairly trivial, but it is useful to avoid opening @(tsee outgoing)
     while still obtaining this fact, in certain proofs."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (dag-previous-in-dag-p dag)
                (dag-previous-are-quorum-p dag quorum)
                (set::in cert dag))
           (equal (set::cardinality (outgoing cert dag))
                  (if (equal (certificate->round cert) 1)
                      0
                    quorum)))
  :enable (outgoing
           cardinality-of-certs-with-authors+round-when-subset
           certificate-previous-in-dag-p
           dag-previous-are-quorum-p-necc)
  :use dag-previous-in-dag-p-necc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-incoming-to-tally-leader-votes
  :short "Relation between the number of incoming certificates
          and the number of `yes' votes to the certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is useful to relate these two formulations of the same number,
     in certain proofs."))
  (equal (set::cardinality (incoming anchor dag))
         (mv-nth 0 (tally-leader-votes
                    (certificate->author anchor)
                    (certs-with-round
                     (1+ (certificate->round anchor))
                     dag))))
  :enable incoming

  :prep-lemmas
  ((defrule cardinality-of-incoming-loop-to-tally-leader-votes
     (implies (certificate-setp voters)
              (equal (set::cardinality (incoming-loop voters leader))
                     (mv-nth 0 (tally-leader-votes leader voters))))
     :induct t
     :enable (tally-leader-votes
              incoming-loop
              set::expensive-rules)
     :hints ('(:use (:instance incoming-loop-subset
                               (prev leader)
                               (certs (set::tail voters)))))
     :disable (incoming-loop-subset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection in-of-certificate-causal-history
  :short "Characterization of the members of a certificate's causal history."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given an unequivocal DAG and a certificate in it,
     the elements of the causal history of the certificate in the DAG
     consists exactly of
     the certificates to which the certificate has a path to."))

  (defthm-certificate-causal-history-flag

    (defthm in-of-certificate-causal-history
      (implies (and (certificate-setp dag)
                    (certificate-set-unequivocalp dag)
                    (set::in cert dag))
               (equal (set::in cert0 (certificate-causal-history cert dag))
                      (and cert0
                           (equal (path-to-author+round
                                   cert
                                   (certificate->author cert0)
                                   (certificate->round cert0)
                                   dag)
                                  cert0))))
      :flag certificate-causal-history)

    (defthm in-of-certificate-set-causal-history
      (implies (and (certificate-setp dag)
                    (certificate-set-unequivocalp dag)
                    (set::subset certs dag))
               (equal (set::in cert0 (certificate-set-causal-history certs dag))
                      (and cert0
                           (equal (path-to-author+round-set
                                   certs
                                   (certificate->author cert0)
                                   (certificate->round cert0)
                                   dag)
                                  cert0))))
      :flag certificate-set-causal-history)

    :hints
    (("Goal"
      :in-theory
      (enable* certificate-causal-history
               certificate-set-causal-history
               path-to-author+round
               path-to-author+round-set
               set::expensive-rules
               path-to-author+round-to-cert-with-author+round
               cert-with-author+round-of-element-when-unequivocal
               round-set-of-certs-with-authors+round
               pos-fix
               nil-not-in-certificate-set
               certs-with-authors+round-subset
               certificate-causal-history-subset
               certificate-set-causal-history-subset
               emptyp-of-certificate-set-fix))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'certificate-causal-history) clause)
       '(:use (:instance round-leq-when-path-to-author+round-set
                         (certs (certs-with-authors+round
                                 (certificate->previous cert)
                                 (+ -1 (certificate->round cert))
                                 dag))
                         (author (certificate->author cert0))
                         (round (certificate->round cert0))))))))

  (in-theory (disable in-of-certificate-causal-history
                      in-of-certificate-set-causal-history)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-causal-history-subset-when-path
  :short "In an unequivocal DAG, if there is a path between two certificates,
          the causal history of the destination of the path is a subset of
          the causal history of the source of the path."
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (addressp author)
                (posp round)
                (path-to-author+round cert author round dag))
           (set::subset (certificate-causal-history
                         (path-to-author+round cert author round dag)
                         dag)
                        (certificate-causal-history cert dag)))
  :enable set::expensive-rules

  :prep-lemmas
  ((defrule lemma
     (implies (and (certificate-setp dag)
                   (certificate-set-unequivocalp dag)
                   (set::in cert dag)
                   (addressp author)
                   (posp round)
                   (path-to-author+round cert author round dag)
                   (set::in cert0
                            (certificate-causal-history
                             (path-to-author+round cert author round dag)
                             dag)))
              (set::in cert0 (certificate-causal-history cert dag)))
     :enable (in-of-certificate-causal-history
              certificate->author-of-path-to-author+round
              certificate->round-of-path-to-author+round
              path-to-author+round-in-dag)
     :use (:instance path-to-author+round-transitive
                     (cert cert)
                     (cert1 (path-to-author+round cert author round dag))
                     (cert2 cert0)))))
