; Aleo Library
;
; Copyright (C) 2024 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEO")

(include-book "certificates")

(local (include-book "lib-ext"))

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

(define get-certificate-with-author+round ((author addressp)
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
    (get-certificate-with-author+round author round (set::tail certs)))
  ///

  (defret certificate->author-of-get-certificate-with-author+round
    (implies cert?
             (equal (certificate->author cert?)
                    (address-fix author)))
    :hints (("Goal" :induct t)))

  (defret certificate->round-of-get-certificate-with-author+round
    (implies cert?
             (equal (certificate->round cert?)
                    (pos-fix round)))
    :hints (("Goal" :induct t)))

  (defruled get-certificate-with-author+round-element-when-not-nil
    (implies (and (certificate-setp certs)
                  (get-certificate-with-author+round author round certs))
             (set::in (get-certificate-with-author+round author round certs)
                      certs))
    :induct t)

  (defruled get-certificate-with-author+round-when-element
    (implies (and (set::in cert certs)
                  (equal (certificate->author cert) author)
                  (equal (certificate->round cert) round))
             (get-certificate-with-author+round author round certs))
    :induct t)

  (defruled get-certificate-with-author+round-when-subset
    (implies (and (get-certificate-with-author+round author round certs0)
                  (set::subset certs0 certs))
             (get-certificate-with-author+round author round certs))
    :induct t
    :enable (get-certificate-with-author+round-when-element
             set::subset))

  (defrule get-certificate-with-author+round-of-insert-iff
    (iff (get-certificate-with-author+round
          author round (set::insert cert certs))
         (or (and (equal (certificate->author cert) author)
                  (equal (certificate->round cert) round))
             (get-certificate-with-author+round author round certs)))
    :induct (set::weak-insert-induction cert certs)
    :enable (get-certificate-with-author+round-when-element))

  (defrule get-certificate-with-author+round-of-union-iff
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (addressp author)
                  (posp round))
             (iff (get-certificate-with-author+round
                   author round (set::union certs1 certs2))
                  (or (get-certificate-with-author+round author round certs1)
                      (get-certificate-with-author+round author round certs2))))
    :induct (set::union certs1 certs2)
    :enable (get-certificate-with-author+round
             set::union)
    :hints ('(:use (:instance lemma (cert (set::head certs1)))))
    :prep-lemmas
    ((defrule lemma
       (implies (certificatep cert)
                cert)
       :rule-classes nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-certificates-with-author ((author addressp)
                                      (certs certificate-setp))
  :returns (certs-with-author certificate-setp)
  :short "Retrieve the set of certificates with a given author from a set."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal author cert.author)
        (set::insert (certificate-fix cert)
                     (get-certificates-with-author author (set::tail certs)))
      (get-certificates-with-author author (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret get-certificates-with-author-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-author certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (defrule in-of-get-certificates-with-author
    (implies (certificate-setp certs)
             (equal (set::in cert (get-certificates-with-author author certs))
                    (and (set::in cert certs)
                         (equal (certificate->author cert) author))))
    :induct t)

  (defrule get-certificates-with-author-of-empty
    (equal (get-certificates-with-author author nil)
           nil))

  (defrule get-certificate-with-author-of-insert
    (implies (and (addressp author)
                  (certificatep cert)
                  (certificate-setp certs))
             (equal (get-certificates-with-author author
                                                  (set::insert cert certs))
                    (if (equal (certificate->author cert) author)
                        (set::insert cert
                                     (get-certificates-with-author author
                                                                   certs))
                      (get-certificates-with-author author certs))))
    :enable (set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy))

  (defrule get-certificate-with-author-of-delete
    (implies (and (addressp author)
                  (certificate-setp certs))
             (equal (get-certificates-with-author author
                                                  (set::delete cert certs))
                    (set::delete cert
                                 (get-certificates-with-author author certs))))
    :enable (set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy))

  (defruled emptyp-of-get-certificates-with-author-if-no-author
    (equal (set::emptyp (get-certificates-with-author author certs))
           (not (set::in author (certificate-set->author-set certs))))
    :induct t
    :enable certificate-set->author-set)

  (defrule get-certificates-with-author-of-intersect
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (get-certificates-with-author author
                                                  (set::intersect certs1
                                                                  certs2))
                    (set::intersect
                     (get-certificates-with-author author certs1)
                     (get-certificates-with-author author certs2))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit))

  (defruled certificate-set->author-set-of-get-certificates-with-author
    (implies (certificate-setp certs)
             (equal (certificate-set->author-set
                     (get-certificates-with-author author certs))
                    (if (set::in author (certificate-set->author-set certs))
                        (set::insert author nil)
                      nil)))
    :induct t
    :enable certificate-set->author-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-certificates-with-round ((round posp)
                                     (certs certificate-setp))
  :returns (certs-with-round certificate-setp)
  :short "Retrieve the set of certificates with a given round from a set."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal round cert.round)
        (set::insert (certificate-fix cert)
                     (get-certificates-with-round round (set::tail certs)))
      (get-certificates-with-round round (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret get-certificates-with-round-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-round certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (defrule in-of-get-certificates-with-round
    (implies (certificate-setp certs)
             (equal (set::in cert (get-certificates-with-round round certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert) round))))
    :induct t)

  (defrule get-certificates-with-round-of-empty
    (equal (get-certificates-with-round round nil)
           nil))

  (defrule get-certificates-with-round-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (get-certificates-with-round round
                                                 (set::insert cert certs))
                    (if (equal (certificate->round cert) round)
                        (set::insert cert
                                     (get-certificates-with-round round
                                                                  certs))
                      (get-certificates-with-round round certs))))
    :induct (set::weak-insert-induction cert certs)
    :enable in-of-get-certificates-with-round)

  (defruled get-certificates-with-round-monotone
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (set::subset certs1 certs2))
             (set::subset (get-certificates-with-round round certs1)
                          (get-certificates-with-round round certs2)))
    :enable (set::expensive-rules
             in-of-get-certificates-with-round))

  (defruled get-certificate-with-author+round-when-author-in-certificates
    (implies (and (certificate-setp certs)
                  (set::in author
                           (certificate-set->author-set
                            (get-certificates-with-round round certs))))
             (get-certificate-with-author+round author round certs))
    :use (:instance set::in-head
                    (x (get-certificates-with-author
                        author (get-certificates-with-round round certs))))
    :enable (set::expensive-rules
             get-certificate-with-author+round-when-element
             emptyp-of-get-certificates-with-author-if-no-author)
    :disable set::in-head)

  (defrule get-certificates-with-round-of-intersect
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (get-certificates-with-round
                     round (set::intersect certs1 certs2))
                    (set::intersect
                     (get-certificates-with-round round certs1)
                     (get-certificates-with-round round certs2))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit))

  (defruled round-set-of-get-certificates-with-round
    (equal (certificate-set->round-set
            (get-certificates-with-round round certs))
           (if (set::emptyp (get-certificates-with-round round certs))
               nil
             (set::insert round nil)))
    :induct t)

  (defruled round-set-of-get-certificates-with-round-possibilities
    (or (equal (certificate-set->round-set
                (get-certificates-with-round round certs))
               nil)
        (equal (certificate-set->round-set
                (get-certificates-with-round round certs))
               (set::insert round nil)))
    :induct t
    :enable certificate-set->round-set)

  (defruled cardinality-of-round-set-of-get-certificates-with-round
    (<= (set::cardinality
         (certificate-set->round-set
          (get-certificates-with-round round certs)))
        1)
    :rule-classes :linear
    :use round-set-of-get-certificates-with-round-possibilities
    :enable set::cardinality)

  (defruled cardinality-of-subset-of-round-set-of-round
    (implies (set::subset certs0
                          (get-certificates-with-round round certs))
             (<= (set::cardinality
                  (certificate-set->round-set certs0))
                 1))
    :rule-classes :linear
    :enable cardinality-of-round-set-of-get-certificates-with-round
    :use ((:instance set::subset-cardinality
                     (x (certificate-set->round-set certs0))
                     (y (certificate-set->round-set
                         (get-certificates-with-round round certs)))))
    :disable set::subset-cardinality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-certificates-with-authors ((authors address-setp)
                                       (certs certificate-setp))
  :returns (certs-with-authors certificate-setp)
  (cond ((set::emptyp authors) nil)
        (t (set::union
            (get-certificates-with-author (set::head authors) certs)
            (get-certificates-with-authors (set::tail authors) certs))))
  :verify-guards :after-returns
  ///

  (defret get-certificates-with-authors-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-authors certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (defrule in-of-get-certificate-with-authors
    (implies (certificate-setp certs)
             (equal (set::in cert
                             (get-certificates-with-authors authors certs))
                    (and (set::in cert certs)
                         (set::in (certificate->author cert) authors))))
    :induct t
    :hints ('(:use (:instance set::in-tail-or-head
                              (a (certificate->author cert))
                              (x authors)))))

  (defruled author-set-of-get-certificates-with-authors
    (implies (and (address-setp authors)
                  (certificate-setp certs))
             (equal (certificate-set->author-set
                     (get-certificates-with-authors authors certs))
                    (set::intersect authors
                                    (certificate-set->author-set certs))))
    :induct t
    :enable (certificate-set->author-set
             set::expensive-rules
             certificate-set->author-set-of-get-certificates-with-author
             set::emptyp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-certificates-with-authors+round ((authors address-setp)
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
                     (get-certificates-with-authors+round authors
                                                          round
                                                          (set::tail certs)))
      (get-certificates-with-authors+round authors
                                           round
                                           (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret get-certificates-with-authors+round-subset
    (set::subset certs-with-authors-and-round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (defrule certificates-authors-of-get-certificates-with-authors+round-subset
    (b* ((returned-authors
          (certificate-set->author-set
           (get-certificates-with-authors+round authors round certs))))
      (set::subset returned-authors authors))
    :induct t)

  (defruled round-set-of-get-certificates-with-authors+round
    (equal (certificate-set->round-set
            (get-certificates-with-authors+round authors round certs))
           (if (set::emptyp
                (get-certificates-with-authors+round authors round certs))
               nil
             (set::insert round nil)))
    :induct t)

  (defruled certificate-set->round-set-of-get-certificates-with-authors+round
    (b* ((rounds (certificate-set->round-set
                  (get-certificates-with-authors+round authors round certs))))
      (implies (not (set::emptyp rounds))
               (equal rounds
                      (set::insert (pos-fix round) nil))))
    :induct t)

  (defrule in-of-get-certificates-with-authors+round
    (implies (certificate-setp certs)
             (equal (set::in cert
                             (get-certificates-with-authors+round authors
                                                                  round
                                                                  certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert) round)
                         (set::in (certificate->author cert) authors))))
    :induct t)

  (defret get-certificates-with-authors+round-subset-with-round
    (set::subset certs-with-authors-and-round
                 (get-certificates-with-round round certs))
    :hyp (certificate-setp certs)
    :hints (("Goal" :in-theory (enable* set::expensive-rules))))

  (defrule get-certificates-with-authors+round-of-empty-authors
    (implies (set::emptyp authors)
             (equal (get-certificates-with-authors+round authors round certs)
                    nil))
    :induct t)

  (defruled get-certificates-with-authors+round-to-authors-of-round
    (implies (certificate-setp certs)
             (equal (get-certificates-with-authors+round authors round certs)
                    (get-certificates-with-authors
                     authors (get-certificates-with-round round certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit))

  (defruled get-certificates-with-authors+round-to-round-of-authors
    (implies (certificate-setp certs)
             (equal (get-certificates-with-authors+round authors round certs)
                    (get-certificates-with-round
                     round (get-certificates-with-authors authors certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit)))
