; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOBFT-STATIC")

(include-book "addresses")
(include-book "transactions")

(include-book "kestrel/fty/pos-set" :dir :system)

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
     which contain proposed transactions along with other information.
     Certificates are the vertices of the DAG.")
   (xdoc::p
    "Certificates have a rich structure,
     but we model only the information needed for our purposes.")
   (xdoc::p
    "In AleoBFT, there is a distinction between proposals and certificates,
     with the latter being an extension of the former with endorsing signatures.
     Currently we do not model proposals, but just certificates,
     because we treat the Narwhal aspects of AleoBFT somewhat abstractly;
     see @(tsee transitions-create-certificate)."))
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
     "The transactions that the validator is proposing
      for inclusion in the blockchain.")
    (xdoc::li
     "The addresses that, together with the previous round number,
      identify the certificates from the previous round
      that this certificate references;
      these define the edges of the DAG.
      It is a system invariant, proved elsewhere,
      that certificates in DAGs are uniquely identified by
      their author and round.")
    (xdoc::li
     "The addresses of the validators that endorsed this certificate,
      by signing it in addition to the author."))
   (xdoc::p
    "We do not model cryptographic signatures explicitly.
     The presence of the author and endorser addresses in a certificate
     models the fact that the author and endorsers signed the certificate
     (more precisely, the proposal that the certificate extends;
     but as explained in @(see certificates),
     we do not model proposals explicitly)."))
  ((author address)
   (round pos)
   (transactions transaction-list)
   (previous address-set)
   (endorsers address-set))
  :pred certificatep)

;;;;;;;;;;;;;;;;;;;;

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
  :hooks (:fix)

  ///

  (defret not-emptyp-of-certificate->signers
    (not (set::emptyp signers))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption certificate-option
  certificate
  :short "Fixtype of optional certificates."
  :pred certificate-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defset certificate-set
  :short "Fixtype of sets of certificates."
  :elt-type certificate
  :elementp-of-nil nil
  :pred certificate-setp

  ///

  (defruled nil-not-in-certificate-set
    (implies (certificate-setp certs)
             (not (set::in nil certs)))
    :use (:instance certificatep-when-in-certificate-setp-binds-free-x
                    (a nil)
                    (x certs))
    :disable certificatep-when-in-certificate-setp-binds-free-x)

  (defruled element-of-certificate-set-not-nil
    (implies (and (certificate-setp certs)
                  (set::in cert certs))
             (not (equal cert nil)))
    :rule-classes ((:forward-chaining :trigger-terms ((set::in cert certs))))
    :enable nil-not-in-certificate-set))

;;;;;;;;;;;;;;;;;;;;

(define cert-set->author-set ((certs certificate-setp))
  :returns (addrs address-setp)
  :short "Lift @(tsee certificate->author) to sets."
  (cond ((set::emptyp (certificate-set-fix certs)) nil)
        (t (set::insert (certificate->author (set::head certs))
                        (cert-set->author-set (set::tail certs)))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule emptyp-of-cert-set->author-set
    (equal (set::emptyp (cert-set->author-set certs))
           (set::emptyp (certificate-set-fix certs)))
    :induct t)

  (defruled certificate->author-in-cert-set->author-set
    (implies (set::in (certificate-fix cert)
                      (certificate-set-fix certs))
             (set::in (certificate->author cert)
                      (cert-set->author-set certs)))
    :induct t)

  (defruled cert-set->author-set-monotone
    (implies (set::subset certs1 (certificate-set-fix certs2))
             (set::subset (cert-set->author-set certs1)
                          (cert-set->author-set certs2)))
    :induct t
    :enable (set::subset
             certificate->author-in-cert-set->author-set))

  (defruled cert-set->author-set-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (cert-set->author-set (set::insert cert certs))
                    (set::insert (certificate->author cert)
                                 (cert-set->author-set certs))))
    :induct (set::weak-insert-induction cert certs)
    :enable certificate->author-in-cert-set->author-set)

  (defruled cert-set->author-set-of-union
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (cert-set->author-set (set::union certs1 certs2))
                    (set::union (cert-set->author-set certs1)
                                (cert-set->author-set certs2))))
    :induct t
    :enable (set::union
             cert-set->author-set-of-insert))

  (defruled same-certificate-author-when-cardinality-leq-1
    (implies (and (<= (set::cardinality (cert-set->author-set certs)) 1)
                  (set::in cert1 (certificate-set-fix certs))
                  (set::in cert2 (certificate-set-fix certs)))
             (equal (certificate->author cert1)
                    (certificate->author cert2)))
    :enable certificate->author-in-cert-set->author-set
    :use (:instance set::same-element-when-cardinality-leq-1
                    (elem1 (certificate->author cert1))
                    (elem2 (certificate->author cert2))
                    (set (cert-set->author-set certs)))))

;;;;;;;;;;;;;;;;;;;;

(define cert-set->round-set ((certs certificate-setp))
  :returns (rounds pos-setp)
  :short "Lift @(tsee certificate->round) to sets."
  (cond ((set::emptyp (certificate-set-fix certs)) nil)
        (t (set::insert (certificate->round (set::head certs))
                        (cert-set->round-set (set::tail certs)))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule emptyp-of-cert-set->round-set
    (equal (set::emptyp (cert-set->round-set certs))
           (set::emptyp (certificate-set-fix certs)))
    :induct t)

  (defruled certificate->round-in-cert-set->round-set
    (implies (set::in (certificate-fix cert)
                      (certificate-set-fix certs))
             (set::in (certificate->round cert)
                      (cert-set->round-set certs)))
    :induct t)

  (defruled cert-set->round-set-monotone
    (implies (set::subset certs1 (certificate-set-fix certs2))
             (set::subset (cert-set->round-set certs1)
                          (cert-set->round-set certs2)))
    :induct t
    :enable (set::subset
             certificate->round-in-cert-set->round-set))

  (defruled cert-set->round-set-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (cert-set->round-set (set::insert cert certs))
                    (set::insert (certificate->round cert)
                                 (cert-set->round-set certs))))
    :induct (set::weak-insert-induction cert certs)
    :enable certificate->round-in-cert-set->round-set)

  (defruled cert-set->round-set-of-union
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (cert-set->round-set (set::union certs1 certs2))
                    (set::union (cert-set->round-set certs1)
                                (cert-set->round-set certs2))))
    :induct t
    :enable (set::union
             cert-set->round-set-of-insert))

  (defruled same-certificate-round-when-cardinality-leq-1
    (implies (and (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (set::in cert1 (certificate-set-fix certs))
                  (set::in cert2 (certificate-set-fix certs)))
             (equal (certificate->round cert1)
                    (certificate->round cert2)))
    :enable certificate->round-in-cert-set->round-set
    :use (:instance set::same-element-when-cardinality-leq-1
                    (elem1 (certificate->round cert1))
                    (elem2 (certificate->round cert2))
                    (set (cert-set->round-set certs)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist certificate-list
  :short "Fixtype of lists of certificates."
  :elt-type certificate
  :true-listp t
  :elementp-of-nil nil
  :pred certificate-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate-with-author+round ((author addressp)
                                       (round posp)
                                       (certs certificate-setp))
  :returns (cert? certificate-optionp)
  :short "Retrieve the certificate from a set
          with a given author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no certificate with the given author and round,
     @('nil') is returned, for no certificate.")
   (xdoc::p
    "If there is a certificate with the given author and round,
     the first one found is returned,
     according to the total ordering of the set.
     However, this function will be used in sets where certificates
     have unique combinations of author and round,
     which justifies the use of `the' above in `Retrieve the certificate...'."))
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
  (in-theory (disable certificate->author-of-certificate-with-author+round))

  (defret certificate->round-of-certificate-with-author+round
    (implies cert?
             (equal (certificate->round cert?)
                    (pos-fix round)))
    :hints (("Goal" :induct t)))
  (in-theory (disable certificate->round-of-certificate-with-author+round))

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
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (addressp author)
                  (posp round))
             (iff (certificate-with-author+round
                   author round (set::union certs1 certs2))
                  (or (certificate-with-author+round author round certs1)
                      (certificate-with-author+round author round certs2))))
    :induct (set::union certs1 certs2)
    :enable (set::union
             certificate-with-author+round-of-insert-iff)
    :hints ('(:use (:instance lemma (cert (set::head certs1)))))
    :prep-lemmas
    ((defrule lemma
       (implies (certificatep cert)
                cert)
       :rule-classes nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-author ((author addressp)
                                  (certs certificate-setp))
  :returns (certs-with-author certificate-setp)
  :short "Retrieve the set of certificates with a given author from a set."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal author cert.author)
        (set::insert (certificate-fix cert)
                     (certificates-with-author author (set::tail certs)))
      (certificates-with-author author (set::tail certs))))
  :verify-guards :after-returns
  ///

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
                         (equal (certificate->author cert) author))))
    :induct t
    :enable cert-set->author-set-of-insert)

  (defruled certificates-with-author-when-emptyp
    (implies (set::emptyp certs)
             (equal (certificates-with-author author certs)
                    nil)))

  (defruled certificate-with-author-of-insert
    (implies (and (addressp author)
                  (certificatep cert)
                  (certificate-setp certs))
             (equal (certificates-with-author author
                                              (set::insert cert certs))
                    (if (equal (certificate->author cert) author)
                        (set::insert cert
                                     (certificates-with-author author
                                                               certs))
                      (certificates-with-author author certs))))
    :enable (in-of-certificates-with-author
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy))

  (defruled certificate-with-author-of-delete
    (implies (and (addressp author)
                  (certificate-setp certs))
             (equal (certificates-with-author author
                                              (set::delete cert certs))
                    (set::delete cert
                                 (certificates-with-author author certs))))
    :enable (in-of-certificates-with-author
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy))

  (defruled emptyp-of-certificates-with-author-if-no-author
    (implies (certificate-setp certs)
             (equal (set::emptyp (certificates-with-author author certs))
                    (not (set::in author (cert-set->author-set certs)))))
    :induct t
    :enable cert-set->author-set)

  (defruled certificates-with-author-of-intersect
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (certificates-with-author author
                                              (set::intersect certs1
                                                              certs2))
                    (set::intersect
                     (certificates-with-author author certs1)
                     (certificates-with-author author certs2))))
    :enable (in-of-certificates-with-author
             set::expensive-rules
             set::double-containment-no-backchain-limit))

  (defruled cert-set->author-set-of-certificates-with-author
    (implies (certificate-setp certs)
             (equal (cert-set->author-set
                     (certificates-with-author author certs))
                    (if (set::in author (cert-set->author-set certs))
                        (set::insert author nil)
                      nil)))
    :induct t
    :enable (cert-set->author-set
             cert-set->author-set-of-insert)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-round ((round posp)
                                 (certs certificate-setp))
  :returns (certs-with-round certificate-setp)
  :short "Retrieve the set of certificates with a given round from a set."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal round cert.round)
        (set::insert (certificate-fix cert)
                     (certificates-with-round round (set::tail certs)))
      (certificates-with-round round (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret certificates-with-round-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-round certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* in-of-certificates-with-author
                                 set::subset
                                 set::expensive-rules))))
  (in-theory (disable certificates-with-round-subset))

  (defruled in-of-certificates-with-round
    (implies (certificate-setp certs)
             (equal (set::in cert (certificates-with-round round certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert) round))))
    :induct t)

  (defruled certificates-with-round-when-emptyp
    (implies (set::emptyp certs)
             (equal (certificates-with-round round certs)
                    nil)))

  (defruled certificates-with-round-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certificates-with-round round
                                             (set::insert cert certs))
                    (if (equal (certificate->round cert) round)
                        (set::insert cert
                                     (certificates-with-round round
                                                              certs))
                      (certificates-with-round round certs))))
    :induct (set::weak-insert-induction cert certs)
    :enable in-of-certificates-with-round)

  (defruled certificates-with-round-monotone
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (set::subset certs1 certs2))
             (set::subset (certificates-with-round round certs1)
                          (certificates-with-round round certs2)))
    :enable (set::expensive-rules
             in-of-certificates-with-round))

  (defruled certificate-with-author+round-when-author-in-round
    (implies (and (certificate-setp certs)
                  (set::in author
                           (cert-set->author-set
                            (certificates-with-round round certs))))
             (certificate-with-author+round author round certs))
    :use (:instance set::in-head
                    (x (certificates-with-author
                        author (certificates-with-round round certs))))
    :enable (set::expensive-rules
             in-of-certificates-with-author
             in-of-certificates-with-round
             certificate-with-author+round-when-element
             emptyp-of-certificates-with-author-if-no-author)
    :disable set::in-head)

  (defruled certificates-with-round-of-intersect
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (certificates-with-round
                     round (set::intersect certs1 certs2))
                    (set::intersect
                     (certificates-with-round round certs1)
                     (certificates-with-round round certs2))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certificates-with-round))

  (defruled round-set-of-certificates-with-round
    (equal (cert-set->round-set
            (certificates-with-round round certs))
           (if (set::emptyp (certificates-with-round round certs))
               nil
             (set::insert round nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled round-set-of-certificates-with-round-possibilities
    (or (equal (cert-set->round-set
                (certificates-with-round round certs))
               nil)
        (equal (cert-set->round-set
                (certificates-with-round round certs))
               (set::insert round nil)))
    :induct t
    :enable (cert-set->round-set
             cert-set->round-set-of-insert))

  (defruled cardinality-of-round-set-of-certificates-with-round
    (<= (set::cardinality
         (cert-set->round-set
          (certificates-with-round round certs)))
        1)
    :rule-classes :linear
    :use round-set-of-certificates-with-round-possibilities
    :enable set::cardinality)

  (defruled cardinality-of-subset-of-round-set-of-round
    (implies (set::subset certs0
                          (certificates-with-round round certs))
             (<= (set::cardinality
                  (cert-set->round-set certs0))
                 1))
    :rule-classes :linear
    :enable (cardinality-of-round-set-of-certificates-with-round
             cert-set->round-set-monotone)
    :use ((:instance set::subset-cardinality
                     (x (cert-set->round-set certs0))
                     (y (cert-set->round-set
                         (certificates-with-round round certs)))))
    :disable set::subset-cardinality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-authors ((authors address-setp)
                                   (certs certificate-setp))
  :returns (certs-with-authors certificate-setp)
  :short "Retrieve the set of certificates with given authors from a set."
  (cond ((set::emptyp authors) nil)
        (t (set::union
            (certificates-with-author (set::head authors) certs)
            (certificates-with-authors (set::tail authors) certs))))
  :verify-guards :after-returns
  ///

  (defret certificates-with-authors-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-authors certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* certificates-with-author-subset
                                 set::subset
                                 set::expensive-rules))))
  (in-theory (disable certificates-with-authors-subset))

  (defruled in-of-certificates-with-authors
    (implies (certificate-setp certs)
             (equal (set::in cert
                             (certificates-with-authors authors certs))
                    (and (set::in cert certs)
                         (set::in (certificate->author cert) authors))))
    :induct t
    :enable in-of-certificates-with-author
    :hints ('(:use (:instance set::in-tail-or-head
                              (a (certificate->author cert))
                              (x authors)))))

  (defruled author-set-of-certificates-with-authors
    (implies (and (address-setp authors)
                  (certificate-setp certs))
             (equal (cert-set->author-set
                     (certificates-with-authors authors certs))
                    (set::intersect authors
                                    (cert-set->author-set certs))))
    :induct t
    :enable (cert-set->author-set
             set::expensive-rules
             cert-set->author-set-of-certificates-with-author
             cert-set->author-set-of-union)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-authors+round ((authors address-setp)
                                         (round posp)
                                         (certs certificate-setp))
  :returns (certs-with-authors-and-round certificate-setp)
  :short "Retrieve the certificates from a set
          with author in a given set and with a given round."
  (b* (((when (set::emptyp certs)) nil)
       (cert (set::head certs)))
    (if (and (set::in (certificate->author cert) authors)
             (equal (certificate->round cert) round))
        (set::insert (certificate-fix cert)
                     (certificates-with-authors+round authors
                                                      round
                                                      (set::tail certs)))
      (certificates-with-authors+round authors
                                       round
                                       (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret certificates-with-authors+round-subset
    (set::subset certs-with-authors-and-round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))
  (in-theory (disable certificates-with-authors+round-subset))

  (defruled certificates-authors-of-certificates-with-authors+round-subset
    (b* ((returned-authors
          (cert-set->author-set
           (certificates-with-authors+round authors round certs))))
      (set::subset returned-authors authors))
    :induct t
    :enable cert-set->author-set-of-insert)

  (defruled round-set-of-certificates-with-authors+round
    (equal (cert-set->round-set
            (certificates-with-authors+round authors round certs))
           (if (set::emptyp
                (certificates-with-authors+round authors round certs))
               nil
             (set::insert round nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled cert-set->round-set-of-certificates-with-authors+round
    (b* ((rounds (cert-set->round-set
                  (certificates-with-authors+round authors round certs))))
      (implies (not (set::emptyp rounds))
               (equal rounds
                      (set::insert (pos-fix round) nil))))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled in-of-certificates-with-authors+round
    (implies (certificate-setp certs)
             (equal (set::in cert
                             (certificates-with-authors+round authors
                                                              round
                                                              certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert) round)
                         (set::in (certificate->author cert) authors))))
    :induct t)

  (defret certificates-with-authors+round-subset-with-round
    (set::subset certs-with-authors-and-round
                 (certificates-with-round round certs))
    :hyp (certificate-setp certs)
    :hints
    (("Goal" :in-theory (enable* set::expensive-rules
                                 in-of-certificates-with-round
                                 in-of-certificates-with-authors+round))))
  (in-theory (disable certificates-with-authors+round-subset-with-round))

  (defruled certificates-with-authors+round-of-empty-authors
    (implies (set::emptyp authors)
             (equal (certificates-with-authors+round authors round certs)
                    nil))
    :induct t)

  (defruled certificates-with-authors+round-to-authors-of-round
    (implies (certificate-setp certs)
             (equal (certificates-with-authors+round authors round certs)
                    (certificates-with-authors
                     authors (certificates-with-round round certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certificates-with-round
             in-of-certificates-with-authors
             in-of-certificates-with-authors+round))

  (defruled certificates-with-authors+round-to-round-of-authors
    (implies (certificate-setp certs)
             (equal (certificates-with-authors+round authors round certs)
                    (certificates-with-round
                     round (certificates-with-authors authors certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certificates-with-round
             in-of-certificates-with-authors
             in-of-certificates-with-authors+round)))
