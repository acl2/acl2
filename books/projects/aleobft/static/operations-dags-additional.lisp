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

(include-book "kestrel/utilities/osets" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-dags-additional
  :parents (operations-additional)
  :short "Additional operations on DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are used to formulate and prove correctness,
     not in the definition of the labeled state transition system;
     this is why they are separate from @(see operations-dags).")
   (xdoc::p
    "We introduce operations to return
     the sets of incoming and outgoing certificates of a certificate in a DAG.
     These are more convenient, for certain correctness proof purposes,
     than the expression of these concepts (i.e. incoming and outgoing)
     in the definition of the state transition system.
     We could in fact consider reformulating
     the definition of the state transition system
     to use these two operations."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define incoming ((cert certificatep) (dag certificate-setp))
  :guard (set::in cert dag)
  :returns (certs certificate-setp)
  :short "Set of the certificates in a DAG whose outgoing edges
          are the incoming edges of the given certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, given the edges into @('cert'),
     which are arrows pointing to @('cert'),
     we return the set of certificates from the arrows depart.")
   (xdoc::p
    "In other words, these are the successors of @('cert') in the DAG,
     where `successor' goes the opposite way of the arrows,
     and refers to the `successive' round.
     Perhaps this operations should be renamed @('successors').")
   (xdoc::p
    "These certificates are all in the round just after @('cert').
     We loop through all the certificates in that round,
     and collect the certificates that have the author of @('cert')
     in their set of previous authors."))
  (incoming-loop (certificates-with-round
                  (1+ (certificate->round cert)) dag)
                 (certificate->author cert))

  :prepwork

  ((define incoming-loop ((certs certificate-setp) (prev addressp))
     :returns (incoming-certs certificate-setp)
     :parents nil
     (b* (((when (set::emptyp certs)) nil)
          (cert (set::head certs)))
       (if (set::in prev (certificate->previous cert))
           (set::insert (certificate-fix cert)
                        (incoming-loop (set::tail certs) prev))
         (incoming-loop (set::tail certs) prev)))
     :verify-guards :after-returns

     ///

     (defret incoming-loop-subset
       (set::subset incoming-certs certs)
       :hyp (certificate-setp certs)
       :hints (("Goal"
                :induct t
                :in-theory (enable* set::expensive-rules))))
     (in-theory (disable incoming-loop-subset))

     (defruled incoming-loop-previous-and-member
       (implies (and (certificate-setp certs)
                     (set::in cert (incoming-loop certs prev)))
                (and (set::in cert certs)
                     (set::in prev (certificate->previous cert))))
       :induct t)

     (defruled round-set-of-incoming-loop
       (implies (equal (cert-set->round-set certs)
                       (if (set::emptyp certs)
                           nil
                         (set::insert round nil)))
                (equal (cert-set->round-set (incoming-loop certs prev))
                       (if (set::emptyp (incoming-loop certs prev))
                           nil
                         (set::insert round nil))))
       :induct t
       :enable (cert-set->round-set
                cert-set->round-set-of-insert
                emptyp-of-cert-set->round-set
                set::expensive-rules)
       :hints ('(:use (:instance set::emptyp-when-proper-subset-of-singleton
                                 (x (cert-set->round-set (tail certs)))
                                 (a (certificate->round (head certs)))))))))

  ///

  (defret incoming-subset
    (set::subset certs dag)
    :hyp (certificate-setp dag)
    :hints (("Goal"
             :in-theory (acl2::e/d* (set::expensive-rules
                                     in-of-certificates-with-round)
                                    (incoming-loop-subset))
             :use (:instance incoming-loop-subset
                             (certs (certificates-with-round
                                     (+ 1 (certificate->round cert))
                                     dag))
                             (prev (certificate->author cert))))))
  (in-theory (disable incoming-subset))

  (defret incoming-subset-of-next-round
    (set::subset certs
                 (certificates-with-round
                  (1+ (certificate->round cert))
                  dag))
    :hints (("Goal" :in-theory (enable incoming-loop-subset))))
  (in-theory (disable incoming-subset-of-next-round))

  (defret incoming-same-round
    (<= (set::cardinality (cert-set->round-set certs))
        1)
    :hyp (certificate-setp dag)
    :rule-classes :linear
    :hints (("Goal"
             :use incoming-subset-of-next-round
             :in-theory (e/d (cardinality-of-subset-of-round-set-of-round)
                             (incoming-subset-of-next-round
                              incoming)))))
  (in-theory (disable incoming-same-round))

  (defruled incoming-in-dag
    (implies (and (certificate-setp dag)
                  (set::in cert1 (incoming cert dag)))
             (set::in cert1 dag))
    :enable (incoming
             in-of-certificates-with-round)
    :use (:instance incoming-loop-previous-and-member
                    (cert cert1)
                    (certs (certificates-with-round
                            (1+ (certificate->round cert)) dag))
                    (prev (certificate->author cert))))

  (defruled round-set-of-incoming
    (equal (cert-set->round-set (incoming cert dag))
           (if (set::emptyp (incoming cert dag))
               nil
             (set::insert (1+ (certificate->round cert)) nil)))
    :enable round-set-of-certificates-with-round
    :use (:instance round-set-of-incoming-loop
                    (prev (certificate->author cert))
                    (certs (certificates-with-round
                            (+ 1 (certificate->round cert)) dag))
                    (round (+ 1 (certificate->round cert))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define outgoing ((cert certificatep) (dag certificate-setp))
  :guard (set::in cert dag)
  :returns (certs certificate-setp)
  :short "Set of the certificates in a DAG whose incoming edges
          are the outgoing edges of the given certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, given the edges out of @('cert'),
     which are arrows departing from @('cert'),
     we return the set of certificates that the arrows point to.")
   (xdoc::p
    "In other words, these are the predecessors of @('cert') in the DAG,
     where `predecessor' goes the opposite way of the arrows,
     and refers to the `preceding' round.
     Perhaps this operation should be renamed @('predecessors').")
   (xdoc::p
    "If the certificate is at round 1, we return the empty set.
     Otherwise, we return the certificates at the previous round
     that are authored by the previous authors in the certificate.
     All the returned certificates are in the round just before @('cert')."))
  (if (equal (certificate->round cert) 1)
      nil
    (certificates-with-authors+round (certificate->previous cert)
                                         (1- (certificate->round cert))
                                         dag))
  :guard-hints (("Goal" :in-theory (enable posp)))

  ///

  (defret outgoing-subset
    (set::subset certs dag)
    :hyp (certificate-setp dag)
    :hints
    (("Goal" :in-theory (enable certificates-with-authors+round-subset))))
  (in-theory (disable outgoing-subset))

  (defret outgoing-subset-of-previous-round
    (set::subset certs
                 (certificates-with-round
                  (1- (certificate->round cert))
                  dag))
    :hyp (certificate-setp dag)
    :hints
    (("Goal"
      :in-theory (enable certificates-with-authors+round-subset-with-round))))
  (in-theory (disable outgoing-subset-of-previous-round))

  (defruled outgoing-in-dag
    (implies (and (certificate-setp dag)
                  (set::in cert1 (outgoing cert dag)))
             (set::in cert1 dag))
    :enable in-of-certificates-with-authors+round)

  (defruled round-in-outgoing-is-one-less
    (implies (and (certificate-setp dag)
                  (set::in cert1 (outgoing cert dag)))
             (equal (certificate->round cert1)
                    (1- (certificate->round cert))))
    :enable in-of-certificates-with-authors+round)

  (defruled round-set-of-outgoing
    (equal (cert-set->round-set (outgoing cert dag))
           (if (set::emptyp (outgoing cert dag))
               nil
             (set::insert (1- (certificate->round cert)) nil)))
    :enable round-set-of-certificates-with-authors+round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate-previous-in-dag-p ((cert certificatep)
                                       (dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if all the previous certificates
          referenced by a given certificate
          are in a given DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "The check succeeds immediately if the certificate's round number is 1.
     In that case, it is an invariant (proved elsewhere)
     that certificates in round 1 reference no previous certificates;
     therefore, the requirement is trivially satisfied.")
   (xdoc::p
    "For the more common case in which the certificate's round number is not 1,
     we retrieve all the certificates from the DAG at the previous round,
     we obtain their set of authors,
     and we check that those are a superset of
     the set of previous certificate authors in the certificate."))
  (b* (((certificate cert) cert))
    (or (equal cert.round 1)
        (set::subset cert.previous
                     (cert-set->author-set
                      (certificates-with-round (1- cert.round) dag)))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  ///

  (defruled certificate-previous-in-dag-p-when-round-1
    (implies (equal (certificate->round cert) 1)
             (certificate-previous-in-dag-p cert dag)))

  (defruled certificate-previous-in-dag-p-when-subset
    (implies (and (certificate-previous-in-dag-p cert dag)
                  (set::subset dag dag1)
                  (certificate-setp dag)
                  (certificate-setp dag1))
             (certificate-previous-in-dag-p cert dag1))
    :enable (certificates-with-round-monotone
             cert-set->author-set-monotone
             set::subset-transitive)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-previous-in-dag-p ((dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if the previous certificates of each certificate in a DAG
          are also all in the DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, this checks if the DAG is closed
     with respect to the previous certificates.
     This ensures the absence of ``dangling'' edges."))
  (forall (cert)
          (implies (set::in cert dag)
                   (certificate-previous-in-dag-p cert dag)))
  ///

  (defruled dag-previous-in-dag-p-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp dag)
                  (dag-previous-in-dag-p dag)
                  (certificate-previous-in-dag-p cert dag))
             (dag-previous-in-dag-p (set::insert cert dag)))
    :use (:instance dag-previous-in-dag-p-necc
                    (cert (dag-previous-in-dag-p-witness (insert cert dag))))
    :enable certificate-previous-in-dag-p-when-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-previous-are-quorum-p ((dag certificate-setp) (quorum natp))
  :returns (yes/no booleanp)
  :short "Check if the previous certificates of every certificate in a DAG
          form a quorum if the round is not 1, or there are none in round 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "The quorum number is passed as input to this predicate."))
  (forall (cert)
          (implies (set::in cert dag)
                   (equal (set::cardinality (certificate->previous cert))
                          (if (equal (certificate->round cert) 1)
                              0
                            quorum)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate-list-pathp ((certs certificate-listp)
                                (dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if a list of zero or more certificates
          are all in a DAG and are connected by paths."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if the list is @('(c1 .. cn)'),
     this predicate says whether
     each @('ci') is in the DAG
     and there is a path from each @('ci') to @('ci+1').
     The predicate is @('t') if the list is empty.
     The predicate is @('t') if the list is a singleton
     whose element is in the DAG;
     no paths are required in this case.
     If there are two or more certificates in the list,
     then there must be paths between each contiguous elements."))
  (b* (((when (endp certs)) t)
       (cert (car certs))
       ((unless (set::in cert dag)) nil)
       ((when (endp (cdr certs))) t)
       (cert1 (cadr certs))
       ((unless (<= (certificate->round cert1)
                    (certificate->round cert)))
        nil)
       ((unless (equal (path-to-author+round cert
                                             (certificate->author cert1)
                                             (certificate->round cert1)
                                             dag)
                       cert1))
        nil))
    (certificate-list-pathp (cdr certs) dag))

  ///

  (defruled certificate-list-pathp-of-nil
    (certificate-list-pathp nil dag))

  (defruled certificate-list-pathp-member-in-dag
    (implies (and (certificate-list-pathp certs dag)
                  (member-equal cert certs))
             (set::in cert dag))
    :induct t
    :enable member-equal)

  (defruled list-in-when-certificate-list-pathp
    (implies (certificate-list-pathp certs dag)
             (set::list-in certs dag))
    :induct t))
