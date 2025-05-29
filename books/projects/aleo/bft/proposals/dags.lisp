; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-PROPOSALS")

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
     as the operations in @(see certificates) do.
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
     If the set is not empty, we first try to find a path
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
    :guard (<= round (certificate->round cert))
    :returns (target-cert? certificate-optionp)
    (b* (((when (> (pos-fix round) (certificate->round cert))) nil)
         ((when (= (certificate->round cert)
                   (pos-fix round)))
          (and (equal (certificate->author cert)
                      (address-fix author))
               (certificate-fix cert)))
         (prev-certs
          (certs-with-authors+round (certificate->previous cert)
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
    :guard (pos-set->=-pos (cert-set->round-set certs) round)
    :returns (target-cert? certificate-optionp)
    (and (not (set::emptyp (certificate-set-fix certs)))
         (or (path-to-author+round (set::head certs) author round dag)
             (path-to-author+round-set (set::tail certs) author round dag)))
    :measure (acl2::nat-list-measure (list
                                      (pos-set-max (cert-set->round-set certs))
                                      1
                                      (set::cardinality certs))))

  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))

  :hints
  (("Goal"
    :in-theory (enable set::cardinality
                       pos-fix
                       cert-set->round-set-monotone
                       certificate->round-in-cert-set->round-set
                       cert-set->round-set-of-certs-with-authors+round)
    :use ((:instance acl2::pos-set-max->=-element
                     (elem (certificate->round (set::head certs)))
                     (set (cert-set->round-set certs)))
          (:instance acl2::pos-set-max->=-subset
                     (set1 (cert-set->round-set (set::tail certs)))
                     (set2 (cert-set->round-set certs))))))

  :guard-hints
  (("Goal" :in-theory (enable posp
                              pos-fix
                              acl2::pos-set->=-pos-element
                              acl2::pos-set->=-pos-subset
                              cert-set->round-set-monotone
                              certificate->round-in-cert-set->round-set
                              cert-set->round-set-of-certs-with-authors+round)))

  ///

  (fty::deffixequiv-mutual path-to-author+round)

  (defret-mutual certificate->author-of-path-to-author+round
    (defret certificate->author-of-path-to-author+round
      (implies target-cert?
               (equal (certificate->author target-cert?)
                      (address-fix author)))
      :fn path-to-author+round)
    (defret certificate->author-of-path-to-author+round-set
      (implies target-cert?
               (equal (certificate->author target-cert?)
                      (address-fix author)))
      :fn path-to-author+round-set))

  (defret-mutual certificate->round-of-path-to-author+round
    (defret certificate->round-of-path-to-author+round
      (implies target-cert?
               (equal (certificate->round target-cert?)
                      (pos-fix round)))
      :fn path-to-author+round)
    (defret certificate->round-of-path-to-author+round-set
      (implies target-cert?
               (equal (certificate->round target-cert?)
                      (pos-fix round)))
      :fn path-to-author+round-set)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines cert-causal-history
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

  (define cert-causal-history ((cert certificatep)
                               (dag certificate-setp))
    :returns (hist certificate-setp)
    (b* (((when (= (certificate->round cert) 1))
          (set::insert (certificate-fix cert) nil))
         (prev-certs (certs-with-authors+round (certificate->previous cert)
                                               (1- (certificate->round cert))
                                               dag))
         (prev-hist (cert-set-causal-history prev-certs dag)))
      (set::insert (certificate-fix cert) prev-hist))
    :measure (acl2::nat-list-measure (list (certificate->round cert)
                                           0
                                           0)))

  (define cert-set-causal-history ((certs certificate-setp)
                                   (dag certificate-setp))
    :returns (hist certificate-setp)
    (cond ((set::emptyp (certificate-set-fix certs)) nil)
          (t (set::union
              (cert-causal-history (set::head certs) dag)
              (cert-set-causal-history (set::tail certs) dag))))
    :measure (acl2::nat-list-measure (list
                                      (pos-set-max (cert-set->round-set certs))
                                      1
                                      (set::cardinality certs))))

  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))

  :hints
  (("Goal"
    :in-theory (enable set::cardinality
                       pos-fix
                       cert-set->round-set-monotone
                       certificate->round-in-cert-set->round-set
                       cert-set->round-set-of-certs-with-authors+round)
    :use ((:instance acl2::pos-set-max->=-element
                     (elem (certificate->round (set::head certs)))
                     (set (cert-set->round-set certs)))
          (:instance acl2::pos-set-max->=-subset
                     (set1 (cert-set->round-set (set::tail certs)))
                     (set2 (cert-set->round-set certs))))))

  :verify-guards :after-returns

  :guard-hints (("Goal" :in-theory (enable posp)))

  ///

  (fty::deffixequiv-mutual cert-causal-history))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cert-previous-in-dag-p ((cert certificatep) (dag certificate-setp))
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
     the set of previous certificate authors referenced by the certificate.")
   (xdoc::p
    "For a given certificate,
     this predicate is preserved by extending the DAG,
     because extending the DAG cannot remove
     any referenced predecessor certificates.
     We prove this in @('cert-previous-in-dag-p-when-subset')."))
  (b* ((round (certificate->round cert))
       (previous (certificate->previous cert)))
    (or (= round 1)
        (set::subset previous
                     (cert-set->author-set
                      (certs-with-round (1- round) dag)))))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defruled cert-previous-in-dag-p-when-subset
    (implies (and (certificate-setp dag)
                  (certificate-setp dag1)
                  (set::subset dag dag1)
                  (cert-previous-in-dag-p cert dag))
             (cert-previous-in-dag-p cert dag1))
    :enable (certs-with-round-monotone
             cert-set->author-set-monotone
             set::subset-transitive)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-closedp ((dag certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if a DAG is backward-closed."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if the previous certificates of each certificate in the DAG
     are all in the DAG.
     This is an invariant of the DAGs of validators, as proved elsewhere.")
   (xdoc::p
    "Adding a certificate whose previous certificates are in the DAG
     preserves the closure of the DAG;
     we prove this in @('dag-closedp-of-insert').
     It might be tempting to try and prove something like")
   (xdoc::codeblock
    "(equal (dag-closedp (set::insert cert dag))"
    "       (and (dag-closedp dag)"
    "            (cert-previous-in-dag-p cert dag)))")
   (xdoc::p
    "but that does not hold, because @('cert') could be
     a predecessor certificate of some certificate in @('dag').
     So instead we prove the right-to-left implication."))
  (forall (cert)
          (implies (set::in cert dag)
                   (cert-previous-in-dag-p cert dag)))

  ///

  (defrule dag-closedp-of-empty
    (dag-closedp nil))

  (defruled dag-closedp-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp dag)
                  (dag-closedp dag)
                  (cert-previous-in-dag-p cert dag))
             (dag-closedp (set::insert cert dag)))
    :enable (cert-previous-in-dag-p-when-subset
             dag-closedp-necc)))

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
  (successors-loop (certs-with-round (1+ (certificate->round cert)) dag)
                   (certificate->author cert))

  :prepwork

  ((define successors-loop ((certs certificate-setp) (prev addressp))
     :returns (succ-certs certificate-setp)
     :parents nil
     (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
          (cert (set::head certs)))
       (if (set::in (address-fix prev)
                    (certificate->previous cert))
           (set::insert cert
                        (successors-loop (set::tail certs) prev))
         (successors-loop (set::tail certs) prev)))
     :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
     :verify-guards :after-returns
     :hooks (:fix)

     ///

     (defret successors-loop-subset
       (set::subset succ-certs certs)
       :hyp (certificate-setp certs)
       :hints (("Goal"
                :induct t
                :in-theory (enable* set::expensive-rules))))

     (defruled in-of-successors-loop
       (implies (certificate-setp certs)
                (equal (set::in cert (successors-loop certs prev))
                       (and (set::in cert certs)
                            (set::in (address-fix prev)
                                     (certificate->previous cert)))))
       :induct t)

     (defruled successors-loop-monotone
       (implies (and (certificate-setp certs1)
                     (certificate-setp certs2)
                     (set::subset certs1 certs2))
                (set::subset (successors-loop certs1 prev)
                             (successors-loop certs2 prev)))
       :enable (in-of-successors-loop
                set::expensive-rules))

     (defruled cert-set->round-set-of-successors-loop
       (implies (and (certificate-setp certs)
                     (equal (cert-set->round-set certs)
                            (if (set::emptyp certs)
                                nil
                              (set::insert round nil))))
                (equal (cert-set->round-set (successors-loop certs prev))
                       (if (set::emptyp (successors-loop certs prev))
                           nil
                         (set::insert round nil))))
       :induct t
       :enable (cert-set->round-set
                cert-set->round-set-of-insert
                set::expensive-rules)
       :hints ('(:use (:instance set::emptyp-when-proper-subset-of-singleton
                                 (x (cert-set->round-set (tail certs)))
                                 (a (certificate->round (head certs)))))))))

  :hooks (:fix)

  ///

  (defret successors-subset-of-next-round
    (set::subset certs
                 (certs-with-round (1+ (certificate->round cert)) dag))
    :hyp (certificate-setp dag))

  (defret successors-subset-of-dag
    (set::subset certs dag)
    :hyp (certificate-setp dag)
    :hints (("Goal"
             :in-theory (e/d (successors-subset-of-next-round)
                             (successors))
             :use (:instance set::subset-transitive
                             (x (successors cert dag))
                             (y (certs-with-round
                                 (1+ (certificate->round cert)) dag))
                             (z dag)))))

  (defruled successors-monotone
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (set::subset dag1 dag2))
             (set::subset (successors cert dag1)
                          (successors cert dag2)))
    :enable (successors-loop-monotone
             certs-with-round-monotone))

  (defruled cert-set->round-set-of-successors
    (implies (certificate-setp dag)
             (equal (cert-set->round-set (successors cert dag))
                    (if (set::emptyp (successors cert dag))
                        nil
                      (set::insert (1+ (certificate->round cert)) nil))))
    :enable cert-set->round-set-of-certs-with-round
    :use (:instance cert-set->round-set-of-successors-loop
                    (prev (certificate->author cert))
                    (certs (certs-with-round
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
    (certs-with-authors+round (certificate->previous cert)
                              (1- (certificate->round cert))
                              dag))
  :guard-hints (("Goal" :in-theory (enable posp)))
  :hooks (:fix)

  ///

  (defret predecessors-subset-of-dag
    (set::subset certs dag)
    :hyp (certificate-setp dag))

  (defret predecessors-subset-of-previous-round
    (set::subset certs
                 (certs-with-round (1- (certificate->round cert)) dag))
    :hyp (certificate-setp dag)
    :hints
    (("Goal"
      :in-theory (enable certs-with-authors+round-to-round-of-authors
                         certs-with-round-monotone))))

  (defruled cert-set->round-set-of-predecessors
    (implies (certificate-setp dag)
             (equal (cert-set->round-set (predecessors cert dag))
                    (if (set::emptyp (predecessors cert dag))
                        nil
                      (set::insert (1- (certificate->round cert)) nil))))
    :enable (certs-with-authors+round-to-round-of-authors
             cert-set->round-set-of-certs-with-round
             posp)))
