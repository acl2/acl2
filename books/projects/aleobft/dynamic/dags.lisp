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

(include-book "certificates")
(include-book "committees")

(include-book "std/basic/two-nats-measure" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/len" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ dags
  :parents (transitions)
  :short "DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "As defined in @(tsee validator-state),
     we model a DAG as a set of certificates.
     Here we introduce operations on DAGs (as certificate sets)
     that are more DAG-specific than the operations on certificate sets
     defined in @(see certificates).
     By `DAG-specific' we mean that take into account the edges of the DAG,
     as opposed to treating the DAG as just a set of vertices
     as the operations in @(see certificates).
     The edges are represented as the @('previous') component of certificates,
     so they are part of the vertices, in terms of data structures."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines path-to-author+round
  :short "Retrieve the certificate with the given author and round
          reachable from a given certificate through the DAG edges."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the certificate is found, it is returned.
     Otherwise, @('nil') is returned.")
   (xdoc::p
    "The guard requires the target round to be no later than
     the round of the current certificate.
     Otherwise, there could be no path,
     since paths never go forward (i.e. from smaller to larger rounds).")
   (xdoc::p
    "If the target round is the same as the one of the current cerfificate,
     we are looking for an empty path in the DAG;
     this is the base case of the recursion.
     In order for an empty path to exist,
     the target certificate must be the current certificate:
     that is, the author of the certificate must be the target one.
     If that is the case, we return the current certificate.
     If the author differs, we return @('nil'): there is no (empty) path.")
   (xdoc::p
    "Otherwise, we must look for a non-empty path.
     We take all the certificates from the previous round
     to which the current certificate has a path of length 1,
     i.e. the previous certificates that the current certificate references.
     Every path from the current certificate must go through
     at least one of these previous certificates.
     We try and find a path from each of these certificates
     to the target round and author, recursively.
     We use a mutually recursive companion function
     to loop through the elements of the set of previous certificates.")
   (xdoc::p
    "The mutually recursive function terminates when the set is empty:
     no path has been found in this case.
     If the set is not empty, it first tries to find a path
     from the minimal (head) element of the set,
     using the mutually recursive companion (the main function).
     If that fails, it recursively tries the rest of the set.")
   (xdoc::p
    "The termination proof for these two mutually recursive functions
     takes a little bit of guidance from the user.
     We use lexicographic measures, as follows.
     When the main function calls the one on the set,
     the round number of the certificates in the set
     is less than the one in the initial certificate;
     the round numbers are all the same in fact,
     but we use a function that returns their maximum,
     which is more flexible (requiring fewer constraints to be considered)
     and suffices to prove termination.
     When the function on the set calls the main function,
     the round number does not change,
     but we just say, in the measures, that
     the main function is ``smaller'' than the one on the set,
     by using the numbers 1 and 0 as the second components of the measures.
     Finally, for the call of the function on the set to itself,
     the set gets smaller, and so we use the cardinality of the set
     as the third component of the measure;
     this does not apply to the main function,
     but we need the measure lists to have the same length
     (otherwise the shorter list would be always less than the longer list),
     and so we just use 0 there.")
   (xdoc::p
    "This function is executable, although it is not particularly efficient.
     But its main purpose is to be a clear specification,
     for which things can be proved conveniently."))

  (define path-to-author+round ((cert certificatep)
                                (author addressp)
                                (round posp)
                                (dag certificate-setp))
    :guard (>= (certificate->round cert) round)
    :returns (previous-cert? certificate-optionp)
    (b* (((unless (mbt (and (posp round)
                            (<= round (certificate->round cert)))))
          nil)
         ((when (= round (certificate->round cert)))
          (and (equal author (certificate->author cert))
               (certificate-fix cert)))
         (prev-certs
          (certificates-with-authors+round (certificate->previous cert)
                                           (1- (certificate->round cert))
                                           dag)))
      (path-to-author+round-set prev-certs author round dag))
    :measure (acl2::nat-list-measure (list (certificate->round cert)
                                           0
                                           0)))

  (define path-to-author+round-set ((certs certificate-setp)
                                    (author addressp)
                                    (round posp)
                                    (dag certificate-setp))
    :guard (pos-set->=-pos (certificate-set->round-set certs) round)
    :returns (previous-cert? certificate-optionp)
    (and (not (set::emptyp certs))
         (or (path-to-author+round (set::head certs) author round dag)
             (path-to-author+round-set (set::tail certs) author round dag)))
    :measure (acl2::nat-list-measure (list (pos-set-max
                                            (certificate-set->round-set certs))
                                           1
                                           (set::cardinality certs))))

  :hints
  (("Goal"
    :in-theory (enable set::cardinality
                       pos-fix
                       certificate-set->round-set-monotone
                       emptyp-of-certificate-set->round-set
                       certificate->round-in-certificate-set->round-set)
    :use
    ((:instance acl2::pos-set-max->=-element
                (elem (certificate->round (set::head certs)))
                (set (certificate-set->round-set certs)))
     (:instance acl2::pos-set-max->=-subset
                (set1 (certificate-set->round-set (set::tail certs)))
                (set2 (certificate-set->round-set certs)))
     (:instance
      certificate-set->round-set-of-certificates-with-authors+round-not-empty
      (authors (certificate->previous cert))
      (round (1- (certificate->round cert)))
      (certs dag)))))

  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       pos-fix
                       acl2::pos-set->=-pos-element
                       acl2::pos-set->=-pos-subset
                       certificate-set->round-set-monotone
                       emptyp-of-certificate-set->round-set
                       certificate->round-in-certificate-set->round-set)
    :use
    (:instance
     certificate-set->round-set-of-certificates-with-authors+round-not-empty
     (authors (certificate->previous cert))
     (round (1- (certificate->round cert)))
     (certs dag))))

  :flag-local nil

  ///

  (defret-mutual certificate->author-of-path-to-author+round
    (defret certificate->author-of-path-to-author+round
      (implies previous-cert?
               (equal (certificate->author previous-cert?)
                      (address-fix author)))
      :fn path-to-author+round)
    (defret certificate->author-of-path-to-author+round-set
      (implies previous-cert?
               (equal (certificate->author previous-cert?)
                      (address-fix author)))
      :fn path-to-author+round-set))
  (in-theory (disable certificate->author-of-path-to-author+round
                      certificate->author-of-path-to-author+round-set))

  (defret-mutual certificate->round-of-path-to-author+round
    (defret certificate->round-of-path-to-author+round
      (implies previous-cert?
               (equal (certificate->round previous-cert?)
                      (pos-fix round)))
      :fn path-to-author+round)
    (defret certificate->round-of-path-to-author+round-set
      (implies previous-cert?
               (equal (certificate->round previous-cert?)
                      (pos-fix round)))
      :fn path-to-author+round-set))
  (in-theory (disable certificate->round-of-path-to-author+round
                      certificate->round-of-path-to-author+round-set)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines certificate-causal-history
  :short "Causal history of a certificate in a DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the set of all the certificates in the DAG
     that the certificate has a path to.
     This includes the certificate itself,
     which has an empty path to itself.
     We calculate the causal history by going backwards through rounds.")
   (xdoc::p
    "We start with the certificate.
     If its round number is 1,
     we stop and return the singleton set with the certificate.
     Since certificates have positive round numbers,
     the DAG cannot have any certificate at round 0.
     It is in fact an invariant that a certificate at round 1
     has no edges to previous certificates,
     although the invariant is not available here.")
   (xdoc::p
    "If the certificate's round number is not 1,
     we retrieve its immediate predecessor certificates,
     which all have the round number that precedes the certificate's.
     We use a mutually recursive companion of this function
     to go through the set of preceding certificates,
     obtaining the causal history for all of them
     (i.e. the union of their causal histories).
     Then we add the current certificate to those combined causal histories,
     and return the result.")
   (xdoc::p
    "This function is executable, but not necessarily efficient:
     it tries out all possible paths in the DAG.
     It is adequate for specification,
     because it has a simple definition
     that is easier to assess and to prove properties about,
     compared to a more efficient definition.
     A more efficient definition could be provided as well,
     and proved equivalent to this one.")
   (xdoc::p
    "The termination measure and proof is similar to
     the one for @(tsee path-to-author+round);
     see that function for details."))

  (define certificate-causal-history ((cert certificatep)
                                      (dag certificate-setp))
    :returns (hist certificate-setp)
    (b* (((certificate cert) cert)
         ((when (= cert.round 1)) (set::insert (certificate-fix cert) nil))
         (prev-certs (certificates-with-authors+round cert.previous
                                                      (1- cert.round)
                                                      dag))
         (prev-hist (certificate-set-causal-history prev-certs dag)))
      (set::insert (certificate-fix cert) prev-hist))
    :measure (acl2::nat-list-measure (list (certificate->round cert)
                                           0
                                           0)))

  (define certificate-set-causal-history ((certs certificate-setp)
                                          (dag certificate-setp))
    :returns (hist certificate-setp)
    (cond ((set::emptyp certs) nil)
          (t (set::union
              (certificate-causal-history (set::head certs) dag)
              (certificate-set-causal-history (set::tail certs) dag))))
    :measure (acl2::nat-list-measure (list (pos-set-max
                                            (certificate-set->round-set certs))
                                           1
                                           (set::cardinality certs))))

  :hints
  (("Goal"
    :in-theory (enable pos-fix
                       set::cardinality
                       certificate-set->round-set-monotone
                       certificate->round-in-certificate-set->round-set)
    :use
    ((:instance acl2::pos-set-max->=-element
                (elem (certificate->round (set::head certs)))
                (set (certificate-set->round-set certs)))
     (:instance acl2::pos-set-max->=-subset
                (set1 (certificate-set->round-set (set::tail certs)))
                (set2 (certificate-set->round-set certs)))
     (:instance
      certificate-set->round-set-of-certificates-with-authors+round-not-empty
      (authors (certificate->previous cert))
      (round (1- (certificate->round cert)))
      (certs dag)))))

  :verify-guards nil ; done below

  :flag-local nil

  ///

  (verify-guards certificate-causal-history
    :hints (("Goal" :in-theory (enable posp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define successors ((cert certificatep) (dag certificate-setp))
  :guard (set::in cert dag)
  :returns (certs certificate-setp)
  :short "Set of the certificates in a DAG that
          are successors of a certificate in a DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the source certificates of the edges in the DAG
     that have the certificate @('cert') as destination.
     These edges are the incoming edges of @('cert').")
   (xdoc::p
    "Here `successor' refers to the fact that
     the returned certificates are
     in the (immediately) successive round of @('cert'),
     even though the directed edges point backwards.")
   (xdoc::p
    "We obtain all the certificates from the successive round,
     and then we filter the ones that have an edge to @('cert'),
     i.e. that have the author of @('cert') in the @('previous') component."))
  (successors-loop (certificates-with-round
                    (1+ (certificate->round cert)) dag)
                   (certificate->author cert))

  :prepwork

  ((define successors-loop ((certs certificate-setp) (prev addressp))
     :returns (successors certificate-setp)
     :parents nil
     (b* (((when (set::emptyp certs)) nil)
          (cert (set::head certs)))
       (if (set::in prev (certificate->previous cert))
           (set::insert (certificate-fix cert)
                        (successors-loop (set::tail certs) prev))
         (successors-loop (set::tail certs) prev)))
     :verify-guards :after-returns

     ///

     (defret successors-loop-subset
       (set::subset successors certs)
       :hyp (certificate-setp certs)
       :hints (("Goal"
                :induct t
                :in-theory (enable* set::expensive-rules))))
     (in-theory (disable successors-loop-subset))

     (defruled in-of-successors-loop
       (implies (certificate-setp certs)
                (equal (set::in cert (successors-loop certs prev))
                       (and (set::in cert certs)
                            (set::in prev (certificate->previous cert)))))
       :induct t)

     (defruled successors-loop-monotone
       (implies (and (certificate-setp certs1)
                     (certificate-setp certs2)
                     (set::subset certs1 certs2))
                (set::subset (successors-loop certs1 prev)
                             (successors-loop certs2 prev)))
       :enable (in-of-successors-loop
                set::expensive-rules)
       :disable successors-loop)

     (defruled certificate-set->round-set-of-successors-loop
       (implies (equal (certificate-set->round-set certs)
                       (if (set::emptyp certs)
                           nil
                         (set::insert round nil)))
                (equal (certificate-set->round-set (successors-loop certs prev))
                       (if (set::emptyp (successors-loop certs prev))
                           nil
                         (set::insert round nil))))
       :induct t
       :enable (certificate-set->round-set
                certificate-set->round-set-of-insert
                emptyp-of-certificate-set->round-set
                set::expensive-rules)
       :hints ('(:use (:instance set::emptyp-when-proper-subset-of-singleton
                                 (x (certificate-set->round-set (tail certs)))
                                 (a (certificate->round (head certs)))))))))

  ///

  (defret successors-subset-of-next-round
    (set::subset certs
                 (certificates-with-round (1+ (certificate->round cert)) dag))
    :hints (("Goal" :in-theory (enable successors-loop-subset))))
  (in-theory (disable successors-subset-of-next-round))

  (defret successors-subset-of-dag
    (set::subset certs dag)
    :hyp (certificate-setp dag)
    :hints (("Goal"
             :in-theory (e/d (certificates-with-round-subset
                              successors-subset-of-next-round)
                             (successors))
             :use (:instance set::subset-transitive
                             (x (successors cert dag))
                             (y (certificates-with-round
                                 (1+ (certificate->round cert)) dag))
                             (z dag)))))
  (in-theory (disable successors-subset-of-dag))

  (defruled successors-monotone
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (set::subset dag1 dag2))
             (set::subset (successors cert dag1)
                          (successors cert dag2)))
    :enable (successors-loop-monotone
             certificates-with-round-monotone))

  (defruled certificate-set->round-set-of-successors
    (implies (certificate-setp dag)
             (equal (certificate-set->round-set (successors cert dag))
                    (if (set::emptyp (successors cert dag))
                        nil
                      (set::insert (1+ (certificate->round cert)) nil))))
    :enable (emptyp-of-certificates-with-round-to-no-round
             certificate-set->round-set-of-certificates-with-round)
    :use (:instance certificate-set->round-set-of-successors-loop
                    (prev (certificate->author cert))
                    (certs (certificates-with-round
                            (+ 1 (certificate->round cert)) dag))
                    (round (+ 1 (certificate->round cert))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define predecessors ((cert certificatep) (dag certificate-setp))
  :guard (set::in cert dag)
  :returns (certs certificate-setp)
  :short "Set of the certificates in a DAG that
          are precedessors of a certificate in a DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the destination certificates of the edges in the DAG
     that have the certificate @('cert') as source.
     These edges are outgoing edges of @('cert').")
   (xdoc::p
    "Here `precedessor' refers to the fact that
     the return certificates are
     in the (immediately) preceding round of @('cert')
     (unless @('cert') is in round 1,
     in which case this function returns the empty set),
     even though the directed edges point backwards.")
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

  (defret predecessors-subset-of-dag
    (set::subset certs dag)
    :hyp (certificate-setp dag)
    :hints
    (("Goal" :in-theory (enable certificates-with-authors+round-subset))))
  (in-theory (disable predecessors-subset-of-dag))

  (defret predecessors-subset-of-previous-round
    (set::subset certs
                 (certificates-with-round (1- (certificate->round cert)) dag))
    :hyp (certificate-setp dag)
    :hints
    (("Goal"
      :in-theory (enable certificates-with-authors+round-to-round-of-authors
                         certificates-with-round-monotone
                         certificates-with-authors-subset))))
  (in-theory (disable predecessors-subset-of-previous-round))

  (defruled certificate-set->round-set-of-predecessors
    (implies (certificate-setp dag)
             (equal (certificate-set->round-set (predecessors cert dag))
                    (if (set::emptyp (predecessors cert dag))
                        nil
                      (set::insert (1- (certificate->round cert)) nil))))
    :enable (certificates-with-authors+round-to-round-of-authors
             emptyp-of-certificates-with-round-to-no-round
             certificate-set->round-set-of-certificates-with-round
             posp)))

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
     the set of previous certificate authors in the certificate.")
   (xdoc::p
    "For a given certificate,
     this predicate is preserved by extending the DAG,
     because extending the DAG cannot remove
     any referenced predecessor certificates."))
  (b* (((certificate cert) cert))
    (or (= cert.round 1)
        (set::subset cert.previous
                     (certificate-set->author-set
                      (certificates-with-round (1- cert.round) dag)))))
  :guard-hints (("Goal" :in-theory (enable posp)))

  ///

  (defruled certificate-previous-in-dag-p-when-subset
    (implies (and (certificate-previous-in-dag-p cert dag)
                  (set::subset dag dag1)
                  (certificate-setp dag)
                  (certificate-setp dag1))
             (certificate-previous-in-dag-p cert dag1))
    :enable (certificates-with-round-monotone
             certificate-set->author-set-monotone
             set::subset-transitive)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-closedp ((dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if a DAG is backward-closed."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the previous certificates of each certificate in the DAG
     are all in the DAG.")
   (xdoc::p
    "Adding a certificate whose previous certificates are in the DAG
     preserves the closure of the DAG.
     It might be tempting to try and prove something like")
   (xdoc::codeblock
    "(equal (dag-closedp (set::insert cert dag))"
    "       (and (dag-closedp dag)"
    "            (certificate-previous-in-dag-p cert dag)))")
   (xdoc::p
    "but that does not hold, because @('cert') could be
     a predecessor certificate of some certificate in @('dag').
     So instead we prove the (right-to-left) implication."))
  (forall (cert)
          (implies (set::in cert dag)
                   (certificate-previous-in-dag-p cert dag)))

  ///

  (defruled dag-closedp-when-emptyp
    (implies (set::emptyp dag)
             (dag-closedp dag)))

  (defruled dag-previous-in-dag-p-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp dag)
                  (dag-closedp dag)
                  (certificate-previous-in-dag-p cert dag))
             (dag-closedp (set::insert cert dag)))
    :enable certificate-previous-in-dag-p-when-subset
    :use (:instance dag-closedp-necc
                    (cert (dag-closedp-witness (set::insert cert dag))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-committees-p ((dag certificate-setp)
                             (blockchain block-listp)
                             (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if the active committee
          at the round of every certificate in a DAG
          can be calculated from a given blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "The intent is that the DAG and blockchain are the ones of a validator,
     and that @('all-vals') are all the validator addresses in the system."))
  (forall (cert)
          (implies (set::in cert dag)
                   (active-committee-at-round (certificate->round cert)
                                              blockchain
                                              all-vals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-predecessor-cardinality-p ((dag certificate-setp)
                                          (blockchain block-listp)
                                          (all-vals address-setp))
  :guard (dag-committees-p dag blockchain all-vals)
  :returns (yes/no booleanp)
  :short "Check if the number of precedessor certificates
          of each certificate in a DAG
          is 0 if the certificate's round is 1
          or the quorum of the active committee at the previous round
          if the certificate's round is not 1."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard ensures that the active committee can be calculated
     for every certificate in the DAG,
     and therefore for the round of the predecessors."))
  (forall (cert)
          (implies (set::in cert dag)
                   (equal (set::cardinality (predecessors cert dag))
                          (if (equal (certificate->round cert) 1)
                              0
                            (b* ((commtt (active-committee-at-round
                                          (1- (certificate->round cert))
                                          blockchain
                                          all-vals)))
                              (committee-quorum commtt))))))
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       pos-fix
                       dag-committees-p-necc)
    :use (:instance active-committee-at-earlier-round-when-at-later-round
                    (later (certificate->round
                            (dag-predecessor-cardinality-p-witness
                             dag blockchain all-vals)))
                    (earlier (1- (certificate->round
                                  (dag-predecessor-cardinality-p-witness
                                   dag blockchain all-vals))))
                    (blocks blockchain)))))
