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
    (b* (((when (= (certificate->round cert) 1))
          (set::insert (certificate-fix cert) nil))
         (prev-certs (certs-with-authors+round (certificate->previous cert)
                                               (1- (certificate->round cert))
                                               dag))
         (prev-hist (certificate-set-causal-history prev-certs dag)))
      (set::insert (certificate-fix cert) prev-hist))
    :measure (acl2::nat-list-measure (list (certificate->round cert)
                                           0
                                           0)))

  (define certificate-set-causal-history ((certs certificate-setp)
                                          (dag certificate-setp))
    :returns (hist certificate-setp)
    (cond ((set::emptyp (certificate-set-fix certs)) nil)
          (t (set::union
              (certificate-causal-history (set::head certs) dag)
              (certificate-set-causal-history (set::tail certs) dag))))
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

  :guard-hints (("Goal" :in-theory (enable posp)))

  :verify-guards :after-returns

  :flag-local nil)
