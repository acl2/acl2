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

(include-book "certificates")

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-certificate-retrieval
  :parents (operations)
  :short "Operations to retrieve certificates from sets of certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We define operations to retrieve certificates, from sets of certificates,
     based on various author and round criteria.
     These operations are primarily used on DAGs in our model,
     which are modeled as sets of certificates
     (satisfying certain invariants
     formalized and proved in @(see correctness)),
     but they are also used on buffers,
     which are also modeled as sets of certificates."))
  :order-subtopics t
  :default-parent t)

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
    :enable (cert-set->author-set
             emptyp-of-certificate-set-fix))

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
