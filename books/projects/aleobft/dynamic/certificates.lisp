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

(include-book "addresses")
(include-book "transactions")

(include-book "kestrel/fty/pos-set" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ certificates
  :parents (states)
  :short "Certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "Validators generate and exchange certificates,
     which contain proposed transactions along with signatures.
     Certificates are the nodes of the DAG,
     in the Narwhal part of AleoBFT.")
   (xdoc::p
    "Certificates have a rich structure,
     but as usual here we model just what is needed for our purposes.")
   (xdoc::p
    "In AleoBFT, there is a distinction between proposals and certificates,
     with the latter being an extension of the former with signatures.
     Currently we do not model proposals, but just certificates,
     because we treat the Narwhal aspects of AleoBFT abstractly here;
     the generation of certificates, and its relation to the ``real'' AleoBFT,
     is explained in the definition of the state transitions.")
   (xdoc::p
    "Beside defining certificates,
     we also introduce operations on (sets of) certificates,
     particularly to retrieve certificates from sets
     according to author and/or round criteria.
     Since DAGs are represented as sets in "
    (xdoc::seetopic "validator-states" "validator states")
    ", these operations are usable (and in fact mainly used) on DAGs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod certificate
  :short "Fixtype of certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a certificate as consisting of:")
   (xdoc::ol
    (xdoc::li
     "The address of the validator who authored the certificate.")
    (xdoc::li
     "The round number of the certificate.")
    (xdoc::li
     "The transactions that the certificate is proposing
      for inclusion in the blockchain.")
    (xdoc::li
     "The addresses that, together with the previous round number,
      identify the certificates from the previous round
      that this certificate is based on.
      (More on this below.)")
    (xdoc::li
     "The addresses of the validators that endorsed this certificate,
      by signing it in addition to the author."))
   (xdoc::p
    "A validator generates at most one certificate per round.
     Thus, the combination of author and round number identifies
     (at most) a unique certificate in a DAG.
     This is a critical and non-trivial property,
     which we prove as an invariant (elsewhere).")
   (xdoc::p
    "A certificate is a vertex of the DAG.
     The @('previous') component of this fixtype models
     the edges of the DAG, from this certificate to
     the certificates in the previous round
     with the authors specified by the set of addresses.
     Because of the invariant mentioned above,
     those certificates are uniquely determined.")
   (xdoc::p
    "Since we model the exchange of proposals and signatures
     at a high level here,
     we do not distinguish between batch headers and batch certificates,
     and instead model certificates directly,
     as containing the information that is relevant to our model.")
   (xdoc::p
    "We do not model cryptographic signatures explicitly.
     The presence of the author and endorser addresses in a certificate
     models the fact that they signed the certificate
     (more precisely, the proposal that the certificate extends,
     but again we do not model proposals, only certificates)."))
  ((author address)
   (round pos)
   (transactions transaction-list)
   (previous address-set)
   (endorsers address-set))
  :pred certificatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset certificate-set
  :short "Fixtype of sets of certificates."
  :elt-type certificate
  :elementp-of-nil nil
  :pred certificate-setp)

;;;;;;;;;;;;;;;;;;;;

(define certificate-set->author-set ((certs certificate-setp))
  :returns (addrs address-setp)
  :short "Lift @(tsee certificate->author) to sets."
  (cond ((set::emptyp certs) nil)
        (t (set::insert (certificate->author (set::head certs))
                        (certificate-set->author-set (set::tail certs)))))
  :verify-guards :after-returns
  ///

  (defruled certificate->author-in-certificate-set->author-set
    (implies (set::in cert certs)
             (set::in (certificate->author cert)
                      (certificate-set->author-set certs)))
    :induct t)

  (defruled certificate-set->author-set-of-insert
    (equal (certificate-set->author-set (set::insert cert certs))
           (set::insert (certificate->author cert)
                        (certificate-set->author-set certs)))
    :induct t
    :enable (set::in
             certificate->author-in-certificate-set->author-set))

  (defruled certificate-set->author-set-of-union
    (equal (certificate-set->author-set (set::union certs1 certs2))
           (set::union (certificate-set->author-set certs1)
                       (certificate-set->author-set (set::sfix certs2))))
    :induct t
    :enable (set::union
             certificate-set->author-set-of-insert))

  (defruled emptyp-of-certificate-set->author-set
    (equal (set::emptyp (certificate-set->author-set certs))
           (set::emptyp certs))
    :induct t)

  (defruled certificate-set->author-set-monotone
    (implies (set::subset certs1 certs2)
             (set::subset (certificate-set->author-set certs1)
                          (certificate-set->author-set certs2)))
    :induct t
    :enable (set::subset
             certificate->author-in-certificate-set->author-set))

  (defruled same-certificate-author-when-cardinality-leq-1
    (implies (and (<= (set::cardinality (certificate-set->author-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
             (equal (certificate->author cert1)
                    (certificate->author cert2)))
    :enable certificate->author-in-certificate-set->author-set
    :use (:instance set::same-element-when-cardinality-leq-1
                    (elem1 (certificate->author cert1))
                    (elem2 (certificate->author cert2))
                    (set (certificate-set->author-set certs)))))

;;;;;;;;;;;;;;;;;;;;

(define certificate-set->round-set ((certs certificate-setp))
  :returns (rounds pos-setp)
  :short "Lift @(tsee certificate->round) to sets."
  (cond ((set::emptyp certs) nil)
        (t (set::insert (certificate->round (set::head certs))
                        (certificate-set->round-set (set::tail certs)))))
  :verify-guards :after-returns
  ///

  (defruled certificate->round-in-certificate-set->round-set
    (implies (set::in cert certs)
             (set::in (certificate->round cert)
                      (certificate-set->round-set certs)))
    :induct t)

  (defruled certificate-set->round-set-of-insert
    (equal (certificate-set->round-set (set::insert cert certs))
           (set::insert (certificate->round cert)
                        (certificate-set->round-set certs)))
    :induct t
    :enable (set::in
             certificate->round-in-certificate-set->round-set))

  (defruled certificate-set->round-set-of-union
    (equal (certificate-set->round-set (set::union certs1 certs2))
           (set::union (certificate-set->round-set certs1)
                       (certificate-set->round-set (set::sfix certs2))))
    :induct t
    :enable (set::union
             certificate-set->round-set-of-insert))

  (defruled emptyp-of-certificate-set->round-set
    (equal (set::emptyp (certificate-set->round-set certs))
           (set::emptyp certs))
    :induct t)

  (defruled certificate-set->round-set-monotone
    (implies (set::subset certs1 certs2)
             (set::subset (certificate-set->round-set certs1)
                          (certificate-set->round-set certs2)))
    :induct t
    :enable (set::subset
             certificate->round-in-certificate-set->round-set))

  (defruled same-certificate-round-when-cardinality-leq-1
    (implies (and (<= (set::cardinality (certificate-set->round-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
             (equal (certificate->round cert1)
                    (certificate->round cert2)))
    :enable certificate->round-in-certificate-set->round-set
    :use (:instance set::same-element-when-cardinality-leq-1
                    (elem1 (certificate->round cert1))
                    (elem2 (certificate->round cert2))
                    (set (certificate-set->round-set certs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption certificate-option
  certificate
  :short "Fixtype of optional certificates."
  :pred certificate-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist certificate-list
  :short "Fixtype of lists of certificates."
  :elt-type certificate
  :true-listp t
  :elementp-of-nil nil
  :pred certificate-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate->signers ((cert certificatep))
  :returns (signers address-setp)
  :short "Signers of a certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the author and the endorsers,
     i.e. all the validators who signed the certificate."))
  (b* (((certificate cert) cert))
    (set::insert cert.author cert.endorsers))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate-with-author+round ((author addressp)
                                       (round posp)
                                       (certs certificate-setp))
  :returns (cert? certificate-optionp)
  :short "Retrieve, from a set of certificates,
          a certificate with a given author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no certificate with the given author and round,
     @('nil') is returned, for no certificate.")
   (xdoc::p
    "If there is a certificate with the given author and round,
     the first one found is returned,
     according to the total ordering of the set.
     However, when a certificate set is unequivocal,
     i.e. it has unique author-round combinations,
     the first certificate found is the only one."))
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs))
       ((when (and (equal author cert.author)
                   (equal round cert.round)))
        (certificate-fix cert)))
    (certificate-with-author+round author round (set::tail certs)))

  ///

  (defret certificate->author-of-certificate-with-author+round
    (implies cert?
             (equal (certificate->author cert?)
                    (address-fix author)))
    :hints (("Goal" :induct t)))

  (defret certificate->round-of-certificate-with-author+round
    (implies cert?
             (equal (certificate->round cert?)
                    (pos-fix round)))
    :hints (("Goal" :induct t)))

  (defruled certificate-with-author+round-element
    (implies (and (certificate-setp certs)
                  (certificate-with-author+round author round certs))
             (set::in (certificate-with-author+round author round certs)
                      certs))
    :induct t)

  (defruled certificate-with-author+round-when-element
    (implies (and (set::in cert certs)
                  (equal (certificate->author cert) author)
                  (equal (certificate->round cert) round))
             (certificate-with-author+round author round certs))
    :induct t)

  (defruled certificate-with-author+round-when-subset
    (implies (and (certificate-with-author+round author round certs0)
                  (set::subset certs0 certs))
             (certificate-with-author+round author round certs))
    :induct t
    :enable (certificate-with-author+round-when-element
             set::subset))

  (defruled certificate-with-author+round-of-insert-iff
    (iff (certificate-with-author+round
          author round (set::insert cert certs))
         (or (and (equal (certificate->author cert) author)
                  (equal (certificate->round cert) round))
             (certificate-with-author+round author round certs)))
    :induct (set::weak-insert-induction cert certs)
    :enable (certificate-with-author+round-when-element))

  (defruled certificate-with-author+round-of-union-iff
    (implies (certificate-setp certs2)
             (iff (certificate-with-author+round
                   author round (set::union certs1 certs2))
                  (or (certificate-with-author+round author round certs1)
                      (certificate-with-author+round author round certs2))))
    :induct t
    :enable (certificate-with-author+round-of-insert-iff
             set::union))

  (defruled certificate-with-author+round-when-delete
    (implies (certificate-with-author+round author
                                            round
                                            (set::delete cert certs))
             (certificate-with-author+round author round certs))
    :enable certificate-with-author+round-when-subset)

  (defruled certificate-with-author+round-of-delete
    (implies (and (certificate-with-author+round author round certs)
                  (or (not (equal (certificate->author cert) author))
                      (not (equal (certificate->round cert) round))))
             (certificate-with-author+round author
                                            round
                                            (set::delete cert certs)))
    :induct t
    :enable (set::delete
             certificate-with-author+round-of-insert-iff)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-author ((author addressp)
                                  (certs certificate-setp))
  :returns (certs-with-author certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given author."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal (address-fix author) cert.author)
        (set::insert (certificate-fix cert)
                     (certificates-with-author author (set::tail certs)))
      (certificates-with-author author (set::tail certs))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv certificates-with-author
    :args ((author addressp)))

  (defret certificates-with-author-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-author certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (in-theory (disable certificates-with-author-subset))

  (defruled in-of-certificates-with-author
    (implies (certificate-setp certs)
             (equal (set::in cert (certificates-with-author author certs))
                    (and (set::in cert certs)
                         (equal (certificate->author cert)
                                (address-fix author)))))
    :induct t)

  (defruled in-certificate-set->author-set-iff-certificates-with-author
    (implies (and (certificate-setp certs)
                  (addressp author))
             (iff (set::in author (certificate-set->author-set certs))
                  (not (set::emptyp (certificates-with-author author certs)))))
    :induct t
    :enable certificate-set->author-set)

  (defruled certificates-with-author-when-emptyp
    (implies (set::emptyp certs)
             (equal (certificates-with-author author certs)
                    nil)))

  (defruled certificate-with-author-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certificates-with-author author
                                              (set::insert cert certs))
                    (if (equal (certificate->author cert)
                               (address-fix author))
                        (set::insert cert
                                     (certificates-with-author author
                                                               certs))
                      (certificates-with-author author certs))))
    :enable (in-of-certificates-with-author
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable (certificates-with-author))

  (defruled certificate-with-author-of-delete
    (implies (certificate-setp certs)
             (equal (certificates-with-author author
                                              (set::delete cert certs))
                    (set::delete cert
                                 (certificates-with-author author certs))))
    :enable (in-of-certificates-with-author
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable certificates-with-author)

  (defruled certificate-with-author+round-in-certificates-with-author
    (implies (and (certificate-setp certs)
                  (certificate-with-author+round author round certs))
             (set::in (certificate-with-author+round author round certs)
                      (certificates-with-author author certs)))
    :enable (in-of-certificates-with-author
             certificate-with-author+round-element)
    :disable certificates-with-author)

  (defruled no-certificate-with-author+round-if-no-certificates-with-author
    (implies (and (certificate-setp certs)
                  (equal (certificates-with-author author certs)
                         nil))
             (not (certificate-with-author+round author round certs)))
    :use certificate-with-author+round-in-certificates-with-author
    :disable certificates-with-author))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-round ((round posp)
                                 (certs certificate-setp))
  :returns (certs-with-round certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given round."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal (pos-fix round) cert.round)
        (set::insert (certificate-fix cert)
                     (certificates-with-round round (set::tail certs)))
      (certificates-with-round round (set::tail certs))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv certificates-with-round
    :args ((round posp)))

  (defret certificates-with-round-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-round certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (in-theory (disable certificates-with-round-subset))

  (defruled in-of-certificates-with-round
    (implies (certificate-setp certs)
             (equal (set::in cert (certificates-with-round round certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert)
                                (pos-fix round)))))
    :induct t)

  (defruled certificates-with-round-monotone
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (set::subset certs1 certs2))
             (set::subset (certificates-with-round round certs1)
                          (certificates-with-round round certs2)))
    :enable (in-of-certificates-with-round
             set::expensive-rules)
    :disable certificates-with-round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-authors+round ((authors address-setp)
                                         (round posp)
                                         (certs certificate-setp))
  :returns (certs-with-authors-and-round certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates
          with author in a given set and with a given round."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (and (set::in cert.author authors)
             (equal cert.round round))
        (set::insert (certificate-fix cert)
                     (certificates-with-authors+round authors
                                                      round
                                                      (set::tail certs)))
      (certificates-with-authors+round authors
                                       round
                                       (set::tail certs))))
  :verify-guards :after-returns

  ///

  (defruled certificate-set->round-set-of-certificates-with-authors+round
    (b* ((rounds (certificate-set->round-set
                  (certificates-with-authors+round authors round certs))))
      (implies (not (set::emptyp rounds))
               (equal rounds
                      (set::insert (pos-fix round) nil))))
    :induct t
    :enable certificate-set->round-set-of-insert))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-signer ((signer addressp)
                                  (certs certificate-setp))
  :returns (certs-with-signer certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates whose signers include a given address."
  (b* (((when (set::emptyp certs)) nil)
       (cert (set::head certs)))
    (if (set::in (address-fix signer)
                 (certificate->signers cert))
        (set::insert (certificate-fix cert)
                     (certificates-with-signer signer
                                               (set::tail certs)))
      (certificates-with-signer signer (set::tail certs))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv certificates-with-signer
    :args ((signer addressp)))

  (defruled in-of-certificates-with-signer
    (implies (certificate-setp certs)
             (equal (set::in cert (certificates-with-signer signer certs))
                    (and (set::in cert certs)
                         (set::in (address-fix signer)
                                  (certificate->signers cert)))))
    :induct t)

  (defruled certificates-with-signer-when-emptyp
    (implies (set::emptyp certs)
             (equal (certificates-with-signer signer certs)
                    nil)))

  (defruled certificates-with-signer-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certificates-with-signer signer
                                              (set::insert cert certs))
                    (if (set::in (address-fix signer)
                                 (certificate->signers cert))
                        (set::insert cert
                                     (certificates-with-signer signer
                                                               certs))
                      (certificates-with-signer signer certs))))
    :enable (in-of-certificates-with-signer
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable (certificates-with-signer)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk certificate-set-unequivocalp ((certs certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if a set of certificates is unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the certificates in the set
     have unique combinations of author and round.
     We check that any two certificates in the set
     with the same author and round
     are in fact the same certificates.
     This means that the certificates in the set
     are uniquely identified by their author and round.")
   (xdoc::p
    "This is an invariant on DAGs,
     and in fact on all the certificates in the system,
     enforced by the protocol under suitable fault tolerance conditions.
     Here we formulate the invariant.")
   (xdoc::p
    "The rule @('certificate-set-unequivocalp-of-insert')
     is useful to prove the preservation of non-equivocation
     when a set of certificates is extended.
     Either the added certificate is already in the initial set,
     or the initial set has no certificate with
     the added certificate's author and round."))
  (forall (cert1 cert2)
          (implies (and (set::in cert1 certs)
                        (set::in cert2 certs)
                        (equal (certificate->author cert1)
                               (certificate->author cert2))
                        (equal (certificate->round cert1)
                               (certificate->round cert2)))
                   (equal cert1 cert2)))

  ///

  (defruled certificate-set-unequivocalp-when-subset
    (implies (and (certificate-set-unequivocalp certs)
                  (set::subset certs0 certs))
             (certificate-set-unequivocalp certs0))
    :use (:instance certificate-set-unequivocalp-necc
                    (cert1
                     (mv-nth 0 (certificate-set-unequivocalp-witness certs0)))
                    (cert2
                     (mv-nth 1 (certificate-set-unequivocalp-witness certs0))))
    :enable set::expensive-rules)

  (defruled certificate-set-unequivocalp-when-emptyp
    (implies (set::emptyp certs)
             (certificate-set-unequivocalp certs)))

  (defruled certificate-set-unequivocalp-of-insert
    (implies (certificate-setp certs)
             (equal (certificate-set-unequivocalp (set::insert cert certs))
                    (and (certificate-set-unequivocalp certs)
                         (or (set::in cert certs)
                             (not (certificate-with-author+round
                                   (certificate->author cert)
                                   (certificate->round cert)
                                   certs))))))
    :use (if-part only-if-part)
    :enable certificate-set-unequivocalp-when-subset

    :prep-lemmas

    ((defruled if-part
       (implies (and (certificate-set-unequivocalp certs)
                     (or (set::in cert certs)
                         (not (certificate-with-author+round
                               (certificate->author cert)
                               (certificate->round cert)
                               certs))))
                (certificate-set-unequivocalp (set::insert cert certs)))
       :use (:instance certificate-set-unequivocalp-necc
                       (cert1 (mv-nth 0 (certificate-set-unequivocalp-witness
                                         (set::insert cert certs))))
                       (cert2 (mv-nth 1 (certificate-set-unequivocalp-witness
                                         (set::insert cert certs))))
                       (certs certs))
       :enable certificate-with-author+round-when-element)

     (defruled only-if-part
       (implies (and (certificate-setp certs)
                     (certificate-set-unequivocalp (set::insert cert certs)))
                (or (set::in cert certs)
                    (not (certificate-with-author+round
                          (certificate->author cert)
                          (certificate->round cert)
                          certs))))
       :use (:instance certificate-set-unequivocalp-necc
                       (cert1 cert)
                       (cert2 (certificate-with-author+round
                               (certificate->author cert)
                               (certificate->round cert)
                               certs))
                       (certs (set::insert cert certs)))
       :enable certificate-with-author+round-element))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk certificate-sets-unequivocalp ((certs1 certificate-setp)
                                          (certs2 certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if two sets of certificates are mutually unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee certificate-set-unequivocalp)
     (note the singular `set' vs. the plural `sets'),
     but checks certificates from different sets.
     It requires that
     if both sets have certificates with the same author and round,
     the certificates must be equal.")
   (xdoc::p
    "This is an invariant that applies across DAGs of different validators.
     Here we just formulate that invariant.")
   (xdoc::p
    "Note that this invariant does not imply that the two sets are unequivocal:
     one set may well have multiple different certificates
     with the same author and round,
     so long as that combination of author and round
     does not appear in the other set.")
   (xdoc::p
    "The rule @('certificate-sets-unequivocalp-of-insert')
     is useful to prove the preservation of mutual non-equivocation
     when one of the two sets of certificates is extended.
     This is similar to @('certificate-set-unequivocalp-of-insert')
     in @(tsee certificate-set-unequivocalp),
     but more complicated due to the presence of two sets.
     Either the new certificate is already in the set being extended,
     or it is in the set not being extended,
     or the set not being extended has no certificate with
     the added certificate's author and round.
     For the second of these three cases,
     we need the additional hypothesis that
     the set not being extended is unequivocal.
     Otherwise, consider the situation of an empty first,
     a second set consisting of two equivocal certificates,
     and the addition of one of these two certificates to the first set:
     the resulting pair of sets is equivocal;
     but the non-equivocation of the second set prevents that."))
  (forall (cert1 cert2)
          (implies (and (set::in cert1 certs1)
                        (set::in cert2 certs2)
                        (equal (certificate->author cert1)
                               (certificate->author cert2))
                        (equal (certificate->round cert1)
                               (certificate->round cert2)))
                   (equal cert1 cert2)))

  ///

  (defruled certificate-sets-unequivocalp-commutative
    (equal (certificate-sets-unequivocalp certs1 certs2)
           (certificate-sets-unequivocalp certs2 certs1))
    :use (certificate-sets-unequivocalp-commutative-lemma
          (:instance certificate-sets-unequivocalp-commutative-lemma
                     (certs1 certs2) (certs2 certs1)))
    :prep-lemmas
    ((defruled certificate-sets-unequivocalp-commutative-lemma
       (implies (certificate-sets-unequivocalp certs1 certs2)
                (certificate-sets-unequivocalp certs2 certs1))
       :use
       (:instance
        certificate-sets-unequivocalp-necc
        (cert1
         (mv-nth 1 (certificate-sets-unequivocalp-witness certs2 certs1)))
        (cert2
         (mv-nth 0 (certificate-sets-unequivocalp-witness certs2 certs1)))))))

  (defruled certificate-sets-unequivocalp-when-subsets
    (implies (and (certificate-sets-unequivocalp certs1 certs2)
                  (set::subset certs01 certs1)
                  (set::subset certs02 certs2))
             (certificate-sets-unequivocalp certs01 certs02))
    :use (:instance
          certificate-sets-unequivocalp-necc
          (cert1
           (mv-nth 0 (certificate-sets-unequivocalp-witness certs01 certs02)))
          (cert2
           (mv-nth 1 (certificate-sets-unequivocalp-witness certs01 certs02))))
    :enable set::expensive-rules)

  (defruled certificate-sets-unequivocalp-when-emptyp
    (implies (or (set::emptyp certs1)
                 (set::emptyp certs2))
             (certificate-sets-unequivocalp certs1 certs2)))

  (defruled certificate-sets-unequivocalp-of-same-set
    (equal (certificate-sets-unequivocalp certs certs)
           (certificate-set-unequivocalp certs))
    :use (only-if-part if-part)
    :prep-lemmas
    ((defruled only-if-part
       (implies (certificate-sets-unequivocalp certs certs)
                (certificate-set-unequivocalp certs))
       :enable certificate-set-unequivocalp
       :disable certificate-sets-unequivocalp
       :use (:instance certificate-sets-unequivocalp-necc
                       (cert1
                        (mv-nth 0 (certificate-set-unequivocalp-witness certs)))
                       (cert2
                        (mv-nth 1 (certificate-set-unequivocalp-witness certs)))
                       (certs1 certs)
                       (certs2 certs)))
     (defruled if-part
       (implies (certificate-set-unequivocalp certs)
                (certificate-sets-unequivocalp certs certs))
       :use
       (:instance
        certificate-set-unequivocalp-necc
        (cert1
         (mv-nth 0 (certificate-sets-unequivocalp-witness certs certs)))
        (cert2
         (mv-nth 1 (certificate-sets-unequivocalp-witness certs certs)))))))

  (defruled certificate-sets-unequivocalp-of-same-set-converse
    (equal (certificate-set-unequivocalp certs)
           (certificate-sets-unequivocalp certs certs))
    :enable certificate-sets-unequivocalp-of-same-set)

  (theory-invariant
   (incompatible (:rewrite certificate-sets-unequivocalp-of-same-set)
                 (:rewrite certificate-sets-unequivocalp-of-same-set-converse)))

  (defruled certificate-sets-unequivocalp-of-insert
    (implies (and (certificate-setp certs2)
                  (certificate-set-unequivocalp certs2))
             (equal (certificate-sets-unequivocalp (set::insert cert certs1)
                                                   certs2)
                    (and (certificate-sets-unequivocalp certs1 certs2)
                         (or (set::in cert certs1)
                             (set::in cert certs2)
                             (not (certificate-with-author+round
                                   (certificate->author cert)
                                   (certificate->round cert)
                                   certs2))))))
    :use (if-part only-if-part)
    :enable certificate-sets-unequivocalp-when-subsets
    :prep-lemmas
    ((defruled if-part
       (implies (and (certificate-sets-unequivocalp certs1 certs2)
                     (certificate-set-unequivocalp certs2)
                     (or (set::in cert certs1)
                         (set::in cert certs2)
                         (not (certificate-with-author+round
                               (certificate->author cert)
                               (certificate->round cert)
                               certs2))))
                (certificate-sets-unequivocalp
                 (set::insert cert certs1) certs2))
       :use
       ((:instance
         certificate-sets-unequivocalp-necc
         (cert1 (mv-nth 0 (certificate-sets-unequivocalp-witness
                           (insert cert certs1)
                           certs2)))
         (cert2 (mv-nth 1 (certificate-sets-unequivocalp-witness
                           (insert cert certs1)
                           certs2))))
        (:instance
         certificate-set-unequivocalp-necc
         (cert1 cert)
         (cert2 (mv-nth 1 (certificate-sets-unequivocalp-witness
                           (insert cert certs1)
                           certs2)))
         (certs certs2)))
       :enable certificate-with-author+round-when-element)
     (defruled only-if-part
       (implies (and (certificate-setp certs2)
                     (certificate-sets-unequivocalp
                      (set::insert cert certs1) certs2))
                (or (set::in cert certs1)
                    (set::in cert certs2)
                    (not (certificate-with-author+round
                          (certificate->author cert)
                          (certificate->round cert)
                          certs2))))
       :use (:instance certificate-sets-unequivocalp-necc
                       (cert1 cert)
                       (cert2 (certificate-with-author+round
                               (certificate->author cert)
                               (certificate->round cert)
                               certs2))
                       (certs1 (set::insert cert certs1)))
       :enable certificate-with-author+round-element))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-ordered-even-p ((certs certificate-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of certificates has
          strictly increasing (right to left), even round numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee blocks-ordered-even-p),
     but for certificates instead of blocks.
     The reason for having this predicate on certificates is that
     blockchains are extended from sequences of anchors,
     which are lists of certificates;
     the reason why blocks have strictly increasing, even round numbers
     is that the collected lists of anchors also have
     strictly increasing, even round numbers."))
  (b* (((when (endp certs)) t)
       (cert (car certs))
       (round (certificate->round cert))
       ((unless (evenp round)) nil)
       ((when (endp (cdr certs))) t)
       ((unless (> round (certificate->round (cadr certs)))) nil))
    (certificates-ordered-even-p (cdr certs)))
  :hooks (:fix))
