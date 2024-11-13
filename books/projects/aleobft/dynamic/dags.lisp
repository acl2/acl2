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

(include-book "kestrel/utilities/osets" :dir :system)
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
                      certificate->round-of-path-to-author+round-set))

  (defret-mutual path-to-author+round-in-dag
    (defret path-to-author+round-in-dag
      (implies previous-cert?
               (set::in previous-cert? dag))
      :hyp (and (certificate-setp dag)
                (set::in cert dag))
      :fn path-to-author+round)
    (defret path-to-author+round-set-in-dag
      (implies previous-cert?
               (set::in previous-cert? dag))
      :hyp (and (certificate-setp dag)
                (set::subset certs dag))
      :fn path-to-author+round-set)
    :hints (("Goal" :in-theory (enable* certificates-with-authors+round-subset
                                        set::expensive-rules))))
  (in-theory (disable path-to-author+round-in-dag
                      path-to-author+round-set-in-dag))

  (defret-mutual round-leq-when-path-to-author+round
    (defret round-leq-when-path-to-author+round
      (implies previous-cert?
               (<= round (certificate->round cert)))
      :fn path-to-author+round
      :rule-classes :linear)
    (defret round-leq-when-path-to-author+round-set
      (implies previous-cert?
               (<= round (pos-set-max (certificate-set->round-set certs))))
      :fn path-to-author+round-set
      :rule-classes :linear)
    :hints
    (("Goal"
      :in-theory (enable* certificate->round-in-certificate-set->round-set
                          certificate-set->round-set-monotone))
     '(:use ((:instance acl2::pos-set-max->=-element
                        (set (certificate-set->round-set certs))
                        (elem (certificate->round (set::head certs))))
             (:instance acl2::pos-set-max->=-subset
                        (set1 (certificate-set->round-set (tail certs)))
                        (set2 (certificate-set->round-set certs)))))))
  (in-theory (disable round-leq-when-path-to-author+round
                      round-leq-when-path-to-author+round-set))

  (defruled path-to-author+round-of-self
    (implies (and (certificate-setp dag)
                  (set::in cert dag))
             (equal (path-to-author+round cert
                                          (certificate->author cert)
                                          (certificate->round cert)
                                          dag)
                    cert)))

  (defruled path-to-author+round-set-when-path-to-author+round-of-element
    (implies (and (set::in cert certs)
                  (path-to-author+round cert author round dag))
             (path-to-author+round-set certs author round dag))
    :induct (set::cardinality certs)
    :enable set::cardinality))

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
    :hints (("Goal" :in-theory (enable posp))))

  (defret-mutual certificate-causal-history-subset
    (defret certificate-causal-history-subset
      (set::subset hist dag)
      :hyp (and (certificate-setp dag)
                (set::in cert dag))
      :fn certificate-causal-history)
    (defret certificate-set-causal-history-subset
      (set::subset hist dag)
      :hyp (and (certificate-setp dag)
                (set::subset certs dag))
      :fn certificate-set-causal-history)
    :hints
    (("Goal" :in-theory (enable* set::expensive-rules
                                 certificates-with-authors+round-subset))))
  (in-theory (disable certificate-causal-history-subset
                      certificate-set-causal-history-subset)))

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
                                 (a (certificate->round (head certs)))))))

     (defruled successors-loop-member-and-previous
       (implies (and (certificate-setp certs)
                     (set::in cert (successors-loop certs prev)))
                (and (set::in cert certs)
                     (set::in prev (certificate->previous cert))))
       :induct t)))

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
                    (round (+ 1 (certificate->round cert)))))

  (defruled certificate->round-of-element-of-successors
    (implies (and (certificate-setp dag)
                  (set::in cert1 (successors cert dag)))
             (equal (certificate->round cert1)
                    (1+ (certificate->round cert))))
    :enable (in-of-certificates-with-round
             set::expensive-rules)
    :disable successors
    :use successors-subset-of-next-round))

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
             posp))

  (defruled head-of-predecessors-in-predecessors
    (implies (not (set::emptyp (predecessors cert dag)))
             (set::in (set::head (predecessors cert dag))
                      (predecessors cert dag)))
    :enable predecessors)

  (defruled head-of-predecessors-in-dag
    (implies (and (certificate-setp dag)
                  (not (set::emptyp (predecessors cert dag))))
             (set::in (set::head (predecessors cert dag))
                      dag))
    :use predecessors-subset-of-dag
    :enable set::expensive-rules
    :disable predecessors)

  (defruled round-in-predecessors-is-one-less
    (implies (and (certificate-setp dag)
                  (set::in cert1 (predecessors cert dag)))
             (equal (certificate->round cert1)
                    (1- (certificate->round cert))))
    :enable (in-of-certificates-with-authors+round
             posp))

  (defruled round-of-head-of-predecessors
    (implies (and (certificate-setp dag)
                  (not (set::emptyp (predecessors cert dag))))
             (equal (certificate->round (set::head (predecessors cert dag)))
                    (1- (certificate->round cert))))
    :use (:instance round-in-predecessors-is-one-less
                    (cert1 (set::head (predecessors cert dag))))
    :enable head-of-predecessors-in-predecessors
    :disable predecessors))

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

  (defruled dag-closedp-of-insert
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
                             (blocks block-listp)
                             (all-vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if the active committee
          at the round of every certificate in a DAG
          can be calculated from a given blockchain."
  :long
  (xdoc::topstring
   (xdoc::p
    "The intent is that the DAG and blockchain are the ones of a validator,
     and that @('all-vals') are all the validator addresses in the system.")
   (xdoc::p
    "Besides the auto-generated @('dag-committee-p-necc'),
     we also introduce a variant that helps bind the free variable @('dag')
     when there is a hypothesis saying that a certificate @('cert') is in it."))
  (forall (cert)
          (implies (set::in cert dag)
                   (active-committee-at-round (certificate->round cert)
                                              blocks
                                              all-vals)))

  ///

  (defruled dag-committees-p-necc-bind-dag
    (implies (and (set::in cert dag)
                  (dag-committees-p dag blocks all-vals))
             (active-committee-at-round (certificate->round cert)
                                        blocks
                                        all-vals))
    :enable dag-committees-p-necc
    :disable dag-committees-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-predecessor-cardinality-p ((dag certificate-setp)
                                          (blocks block-listp)
                                          (all-vals address-setp))
  :guard (dag-committees-p dag blocks all-vals)
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
     and therefore for the round of the predecessors.")
   (xdoc::p
    "Since committees are never empty by definition,
     the quorum number is always positive,
     as proved in the return theorem of @(tsee committee-quorum).
     Thus, this predicate guarantees that
     certificates in rounds above 1
     have at least one predecessor."))
  (forall (cert)
          (implies (set::in cert dag)
                   (equal (set::cardinality (predecessors cert dag))
                          (if (equal (certificate->round cert) 1)
                              0
                            (b* ((commtt (active-committee-at-round
                                          (1- (certificate->round cert))
                                          blocks
                                          all-vals)))
                              (committee-quorum commtt))))))
  :guard-hints
  (("Goal"
    :in-theory (enable posp
                       pos-fix
                       dag-committees-p-necc
                       active-committee-at-previous-round-when-at-round)))

  ///

  (defruled not-emptyp-predecessors-when-dag-predecessor-cardinality-p
    (implies (and (dag-predecessor-cardinality-p dag blocks all-vals)
                  (set::in cert dag)
                  (not (equal (certificate->round cert) 1)))
             (not (set::emptyp (predecessors cert dag))))
    :use (dag-predecessor-cardinality-p-necc)
    :enable set::cardinality
    :disable (dag-predecessor-cardinality-p
              dag-predecessor-cardinality-p-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk dag-rounds-in-committees-p ((dag certificate-setp)
                                       (blocks block-listp)
                                       (all-vals address-setp))
  :guard (dag-committees-p dag blocks all-vals)
  :returns (yes/no booleanp)
  :short "Check if the (one or more) authors of
          the certificates in each round of a DAG
          are members of the active committee at that round."
  :long
  (xdoc::topstring
   (xdoc::p
    "The guard guarantees that,
     if there is at least one author in the set,
     which means that there is at least one certificate at the round,
     the active committee can be calculated.
     Showing, as part of guard verification,
     that the committees is not @('nil') requires a few hints:
     we need to exhibit a witness certificate to use @('dag-committees-p-necc'):
     the witness certificate is
     the first one in @(tsee certificates-with-round);
     that set is not empty because of the equivalent hypothesis that
     the set of authors of those certificates is not empty."))
  (forall (round)
          (implies (posp round)
                   (b* ((commtt (active-committee-at-round round
                                                           blocks
                                                           all-vals))
                        (authors (certificate-set->author-set
                                  (certificates-with-round round dag))))
                     (implies (not (set::emptyp authors))
                              (set::subset authors
                                           (committee-members commtt))))))
  :guard-hints
  (("Goal"
    :use ((:instance set::in-head
                     (x (certificates-with-round
                         (dag-rounds-in-committees-p-witness
                          dag blocks all-vals)
                         dag)))
          (:instance dag-committees-p-necc
                     (cert (set::head
                            (certificates-with-round
                             (dag-rounds-in-committees-p-witness
                              dag blocks all-vals)
                             dag)))))
    :in-theory (e/d (emptyp-of-certificate-set->author-set
                     in-of-certificates-with-round)
                    (set::in-head)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-author+round-set-to-path-to-author+round
  :short "In an unequivocal DAG,
          if a certificate has a path to an author and round,
          then any set including the certificate
          has a path to that author and round,
          and it results in the same certificate."
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
                (set::subset certs dag)
                (set::in cert certs)
                (path-to-author+round cert author round dag))
           (equal (path-to-author+round-set certs author round dag)
                  (path-to-author+round cert author round dag)))
  :enable (set::expensive-rules
           path-to-author+round-in-dag
           path-to-author+round-set-in-dag
           certificate->author-of-path-to-author+round
           certificate->author-of-path-to-author+round-set
           certificate->round-of-path-to-author+round
           certificate->round-of-path-to-author+round-set)
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
    "Here @('cert1') is a generic certificate
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
                  (certs (certificates-with-authors+round
                          (certificate->previous cert1)
                          (+ -1 (certificate->round cert1))
                          dag))
                  (author (certificate->author cert))
                  (round (certificate->round cert)))
  :enable (path-to-author+round
           path-to-author+round-of-self
           nil-not-in-certificate-set
           certificates-with-authors+round-subset
           in-of-certificates-with-authors+round
           posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-from-successor
  :short "In an unequivocal DAG,
          there is a path to a certificate
          from each of its successors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is intuitively obvious,
     since @(tsee successors) is based on the DAG edges,
     which define the paths.")
   (xdoc::p
    "We use the @(tsee path-to-previous) theorem to prove this,
     unsurprisingly."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (set::in cert1 (successors cert dag)))
           (equal (path-to-author+round cert1
                                        (certificate->author cert)
                                        (certificate->round cert)
                                        dag)
                  cert))
  :enable (successors
           path-to-previous
           in-of-certificates-with-round)
  :use (:instance successors-loop-member-and-previous
                  (cert cert1)
                  (certs (certificates-with-round
                          (+ 1 (certificate->round cert))
                          dag))
                  (prev (certificate->author cert))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-predecessor
  :short "There is a path from a certificate
          to each of its predecessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is also intuitively obvious,
     since @(tsee predecessors) is based on the DAG edges,
     which define the paths.")
   (xdoc::p
    "We use the @(tsee path-to-previous) theorem to prove this,
     unsurprisingly."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert1 dag)
                (set::in cert (predecessors cert1 dag)))
           (equal (path-to-author+round cert1
                                        (certificate->author cert)
                                        (certificate->round cert)
                                        dag)
                  cert))
  :enable (predecessors
           path-to-previous
           in-of-certificates-with-authors+round
           posp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-head-of-predecessors
  :short "There is a path from a certificate to
          the first of its predecessors,
          assuming that it has predecessors."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialized version of @(tsee path-to-predecessor),
     which we use to prove this theorem."))
  (implies (and (certificate-setp dag)
                (certificate-set-unequivocalp dag)
                (set::in cert dag)
                (not (set::emptyp (predecessors cert dag))))
           (equal (path-to-author+round
                   cert
                   (certificate->author (set::head (predecessors cert dag)))
                   (certificate->round (set::head (predecessors cert dag)))
                   dag)
                  (set::head (predecessors cert dag))))
  :enable (head-of-predecessors-in-predecessors
           path-to-predecessor))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-previous-certificates
  :short "Some theorems about
          retrieving the previous certificates of a certificate
          in unequivocal DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     the previous cerfificates referenced by a certificate
     in a backward-closed subset of a DAG of unequivocal certificates
     are the same in the superset.
     Note that the non-equivocation of the superset
     implies the non-equivocation of the subset,
     but the backward closure of the subset
     does not imply the backward closure of the superset.
     The latter is not needed, in fact.
     The backward closure of the subset establishes the hypothesis of
     @('certificates-with-authors+round-of-unequivocal-superset')
     in @(see unequivocal-certificates-with-authors+round),
     that the previous authors of the certificate
     are all in the round just before the certificate.")
   (xdoc::p
    "The second theorem says that
     the previous certificates referenced by a common certificate
     of two backward-closed unequivocal and mutually unequivocal DAGs
     are the same in the two DAGs.
     The backward closure of the two sets establishes the hypothesis of
     @('certificates-with-authors+round-of-unequivocal-sets')
     in @(see unequivocal-certificates-with-authors+round),
     that the previous authors of the certificate
     are all in the round just before the certificate, in both sets."))

  (defruled previous-certificates-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::in cert dag0)
                  (or (not (equal (certificate->round cert) 1))
                      (set::emptyp (certificate->previous cert))))
             (equal (certificates-with-authors+round
                     (certificate->previous cert)
                     (1- (certificate->round cert))
                     dag)
                    (certificates-with-authors+round
                     (certificate->previous cert)
                     (1- (certificate->round cert))
                     dag0)))
    :enable (certificate-previous-in-dag-p
             certificates-with-authors+round-when-emptyp
             posp)
    :use ((:instance dag-closedp-necc
                     (dag dag0))
          (:instance certificates-with-authors+round-of-unequivocal-superset
                     (certs0 dag0)
                     (certs dag)
                     (authors (certificate->previous cert))
                     (round (1- (certificate->round cert))))))

  (defruled previous-certificates-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (set::in cert dag1)
                  (set::in cert dag2)
                  (or (not (equal (certificate->round cert) 1))
                      (set::emptyp (certificate->previous cert))))
             (equal (certificates-with-authors+round
                     (certificate->previous cert)
                     (1- (certificate->round cert))
                     dag1)
                    (certificates-with-authors+round
                     (certificate->previous cert)
                     (1- (certificate->round cert))
                     dag2)))
    :enable (certificate-previous-in-dag-p
             certificates-with-authors+round-when-emptyp
             posp)
    :use ((:instance dag-closedp-necc
                     (dag dag1))
          (:instance dag-closedp-necc
                     (dag dag2))
          (:instance certificates-with-authors+round-of-unequivocal-sets
                     (certs1 dag1)
                     (certs2 dag2)
                     (authors (certificate->previous cert))
                     (round (1- (certificate->round cert)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection paths-in-unequivocal-closed-dags
  :short "Some theorems about paths in unequivocal, backward-closed DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     paths from a certificate
     in a backward-closed subset of a DAG of unequivocal certificates
     are the same in the superset.
     As proved in @('previous-certificates-of-unequivocal-superdag')
     in @(see unequivocal-previous-certificates),
     the predecessors are the same in the superset,
     because of the backward closure.
     The same argument can be applied to the predecessors of the predecessors,
     and that covers all paths.
     That is the case not just for paths that reach certificates,
     but also for paths that do not reach cdertificates:
     if the smaller DAG has no path from a certificate
     to a certain author and round,
     neither does the larger DAG;
     if it did, the backward closure would imply that
     the smaller DAG must have a path too.")
   (xdoc::p
    "The second theorem says that
     the paths from a common certificate
     of two backward-closed unequivocal and mutually unequivocal DAGs
     are the same in the two DAGs.
     As proved in @('previous-certificates-of-unequivocal-dags')
     in @(see unequivocal-previous-certificates),
     the predecessors are the same in the two DAGs,
     because of the backward closure.
     The same argument can be applied to the predecessors of the predecessors,
     and that covers all paths.
     That is the case not just for paths that reach certificates,
     but also for paths that do not reach cdertificates:
     if one DAG has no path from a certificate
     to a certain author and round,
     neither does the other DAG;
     while the other one had a path,
     if it did, the backward closure would imply that
     the first DAG must have a path too."))

  (defruled path-to-author+round-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::in cert dag0))
             (equal (path-to-author+round cert author round dag)
                    (path-to-author+round cert author round dag0)))
    :prep-lemmas
    ((defthm-path-to-author+round-flag
       (defthm path-to-author+round-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag1)
                       (set::subset dag dag1)
                       (certificate-set-unequivocalp dag1)
                       (dag-closedp dag)
                       (set::in cert dag))
                  (equal (path-to-author+round cert author round dag1)
                         (path-to-author+round cert author round dag)))
         :flag path-to-author+round)
       (defthm path-to-author+round-set-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag1)
                       (set::subset dag dag1)
                       (certificate-set-unequivocalp dag1)
                       (dag-closedp dag)
                       (set::subset certs dag))
                  (equal (path-to-author+round-set certs author round dag1)
                         (path-to-author+round-set certs author round dag)))
         :flag path-to-author+round-set)
       :hints (("Goal"
                :in-theory
                (enable* path-to-author+round
                         path-to-author+round-set
                         set::expensive-rules
                         certificates-with-authors+round-subset
                         previous-certificates-of-unequivocal-superdag))))))

  (defruled path-to-author+round-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (set::in cert dag1)
                  (set::in cert dag2))
             (equal (path-to-author+round cert author round dag1)
                    (path-to-author+round cert author round dag2)))
    :prep-lemmas
    ((defthm-path-to-author+round-flag
       (defthm path-to-author+round-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag2)
                       (certificate-set-unequivocalp dag)
                       (certificate-set-unequivocalp dag2)
                       (certificate-sets-unequivocalp dag dag2)
                       (dag-closedp dag)
                       (dag-closedp dag2)
                       (set::in cert dag)
                       (set::in cert dag2))
                  (equal (path-to-author+round cert author round dag2)
                         (path-to-author+round cert author round dag)))
         :flag path-to-author+round)
       (defthm path-to-author+round-set-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag2)
                       (certificate-set-unequivocalp dag)
                       (certificate-set-unequivocalp dag2)
                       (certificate-sets-unequivocalp dag dag2)
                       (dag-closedp dag)
                       (dag-closedp dag2)
                       (set::subset certs dag)
                       (set::subset certs dag2))
                  (equal (path-to-author+round-set certs author round dag2)
                         (path-to-author+round-set certs author round dag)))
         :flag path-to-author+round-set)
       :hints (("Goal"
                :in-theory
                (enable* path-to-author+round
                         path-to-author+round-set
                         set::expensive-rules
                         previous-certificates-of-unequivocal-dags))
               (cond
                ((acl2::occur-lst '(acl2::flag-is 'path-to-author+round) clause)
                 '(:use ((:instance
                          certificates-with-authors+round-subset
                          (certs dag)
                          (authors (certificate->previous cert))
                          (round (1- (certificate->round cert))))
                         (:instance
                          certificates-with-authors+round-subset
                          (certs dag2)
                          (authors (certificate->previous cert))
                          (round (1- (certificate->round cert)))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-author+round-to-certificate-with-author+round
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
                  (certificate-with-author+round author round dag)))
  :enable (certificate->author-of-path-to-author+round
           certificate->round-of-path-to-author+round
           path-to-author+round-in-dag)
  :use (:instance certificate-with-author+round-of-element-when-unequivocal
                  (certs dag)
                  (cert (path-to-author+round cert author round dag))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled path-to-author+round-transitive
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
                  cert2))
  :prep-lemmas
  ((defthm-path-to-author+round-flag
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
        path-to-author+round-to-certificate-with-author+round
        certificate-with-author+round-of-element-when-unequivocal
        set::expensive-rules
        nil-not-in-certificate-set
        certificates-with-authors+round-subset
        element-of-certificate-set-not-nil
        round-leq-when-path-to-author+round))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection causal-histories-in-unequivocal-closed-dags
  :short "Some theorems about causal histories in
          unequivocal, backward-closed DAGs."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     the causal history of a certificate
     in a backward-closed subset of an unequivocal DAG
     is the same in the superset.
     That is, causal histories are ``stable'' as DAGs of validators grow.
     New certificates, with their own causal histories,
     may be added as the DAG grows,
     but without affecting histories of certificates already there.")
   (xdoc::p
    "The second theorem says that
     the causal histories of a common certificate
     of two backward-closed, individually and mutually unequivocal DAGs,
     are the same in the two DAGs.
     This is an important property for consistency of blockchains
     across different validators:
     if two validators had different causal histories for the same certificate,
     they could commit different transactions to their blockchains;
     yhis theorem rules out that situation."))

  (defruled certificate-causal-history-of-unequivocal-superdag
    (implies (and (certificate-setp dag0)
                  (certificate-setp dag)
                  (set::subset dag0 dag)
                  (certificate-set-unequivocalp dag)
                  (dag-closedp dag0)
                  (set::in cert dag0))
             (equal (certificate-causal-history cert dag)
                    (certificate-causal-history cert dag0)))
    :prep-lemmas
    ((defthm-certificate-causal-history-flag
       (defthm certificate-causal-history-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag1)
                       (set::subset dag dag1)
                       (certificate-set-unequivocalp dag1)
                       (dag-closedp dag)
                       (set::in cert dag))
                  (equal (certificate-causal-history cert dag1)
                         (certificate-causal-history cert dag)))
         :flag certificate-causal-history)
       (defthm certificate-set-causal-history-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag1)
                       (set::subset dag dag1)
                       (certificate-set-unequivocalp dag1)
                       (dag-closedp dag)
                       (set::subset certs dag))
                  (equal (certificate-set-causal-history certs dag1)
                         (certificate-set-causal-history certs dag)))
         :flag certificate-set-causal-history)
       :hints (("Goal"
                :in-theory
                (enable* certificate-causal-history
                         certificate-set-causal-history
                         set::expensive-rules
                         certificates-with-authors+round-subset
                         previous-certificates-of-unequivocal-superdag))))))

  (defruled certificate-causal-history-of-unequivocal-dags
    (implies (and (certificate-setp dag1)
                  (certificate-setp dag2)
                  (certificate-sets-unequivocalp dag1 dag2)
                  (certificate-set-unequivocalp dag1)
                  (certificate-set-unequivocalp dag2)
                  (dag-closedp dag1)
                  (dag-closedp dag2)
                  (set::in cert dag1)
                  (set::in cert dag2))
             (equal (certificate-causal-history cert dag1)
                    (certificate-causal-history cert dag2)))
    :prep-lemmas
    ((defthm-certificate-causal-history-flag
       (defthm certificate-causal-history-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag2)
                       (certificate-set-unequivocalp dag)
                       (certificate-set-unequivocalp dag2)
                       (certificate-sets-unequivocalp dag dag2)
                       (dag-closedp dag)
                       (dag-closedp dag2)
                       (set::in cert dag)
                       (set::in cert dag2))
                  (equal (certificate-causal-history cert dag2)
                         (certificate-causal-history cert dag)))
         :flag certificate-causal-history)
       (defthm certificate-set-causal-history-lemma
         (implies (and (certificate-setp dag)
                       (certificate-setp dag2)
                       (certificate-set-unequivocalp dag)
                       (certificate-set-unequivocalp dag2)
                       (certificate-sets-unequivocalp dag dag2)
                       (dag-closedp dag)
                       (dag-closedp dag2)
                       (set::subset certs dag)
                       (set::subset certs dag2))
                  (equal (certificate-set-causal-history certs dag2)
                         (certificate-set-causal-history certs dag)))
         :flag certificate-set-causal-history)
       :hints (("Goal"
                :in-theory
                (enable* certificate-causal-history
                         certificate-set-causal-history
                         set::expensive-rules
                         previous-certificates-of-unequivocal-dags))
               (cond
                ((acl2::occur-lst
                  '(acl2::flag-is 'certificate-causal-history) clause)
                 '(:use ((:instance
                          certificates-with-authors+round-subset
                          (certs dag)
                          (authors (certificate->previous cert))
                          (round (1- (certificate->round cert))))
                         (:instance
                          certificates-with-authors+round-subset
                          (certs dag2)
                          (authors (certificate->previous cert))
                          (round (1- (certificate->round cert)))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection in-of-certificate-causal-history
  :short "Characterization of the members of a certificate's causal history."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given an unequivocal DAG and a certificate in it,
     the elements of the causal history of the certificate in the DAG
     consist exactly of the certificates reachable from the certificate."))

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
               path-to-author+round-to-certificate-with-author+round
               certificate-with-author+round-of-element-when-unequivocal
               certificate-set->round-set-of-certificates-with-authors+round
               pos-fix
               posp
               nil-not-in-certificate-set
               certificates-with-authors+round-subset
               certificate-causal-history-subset
               certificate-set-causal-history-subset))
     (cond
      ((acl2::occur-lst '(acl2::flag-is 'certificate-causal-history) clause)
       '(:use (:instance round-leq-when-path-to-author+round-set
                         (certs (certificates-with-authors+round
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-dag-paths-p ((certs certificate-listp)
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
     then there must be a path between each contiguous pair of elements."))
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
    (certificates-dag-paths-p (cdr certs) dag))

  ///

  (defruled certificates-dag-paths-p-of-nil
    (certificates-dag-paths-p nil dag))

  (defruled certificates-dag-paths-p-member-in-dag
    (implies (and (certificates-dag-paths-p certs dag)
                  (member-equal cert certs))
             (set::in cert dag))
    :induct t
    :enable member-equal)

  (defruled list-in-when-certificates-dag-paths-p
    (implies (certificates-dag-paths-p certs dag)
             (set::list-in certs dag))
    :induct t))
