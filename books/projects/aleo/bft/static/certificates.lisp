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
    :enable nil-not-in-certificate-set)

  (defruled head-when-certificate-setp
    (implies (and (certificate-setp certs)
                  (not (set::emptyp certs)))
             (set::head certs))
    :use (nil-not-in-certificate-set
          (:instance set::in-head (x certs)))
    :disable set::in-head))

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

(define cert-with-author+round ((author addressp)
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
     according to the total ordering of the set."))
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       ((certificate cert) (set::head certs))
       ((when (and (equal cert.author (address-fix author))
                   (equal cert.round (pos-fix round))))
        cert))
    (cert-with-author+round author round (set::tail certs)))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))

  ///

  (fty::deffixequiv cert-with-author+round)

  (defret certificate->author-of-cert-with-author+round
    (implies cert?
             (equal (certificate->author cert?)
                    (address-fix author)))
    :hints (("Goal" :induct t)))

  (defret certificate->round-of-cert-with-author+round
    (implies cert?
             (equal (certificate->round cert?)
                    (pos-fix round)))
    :hints (("Goal" :induct t)))

  (defruled cert-with-author+round-element
    (implies (cert-with-author+round author round certs)
             (set::in (cert-with-author+round author round certs)
                      certs))
    :induct t)

  (defruled cert-with-author+round-when-element
    (implies (and (set::in cert certs)
                  (certificate-setp certs)
                  (equal (certificate->author cert) author)
                  (equal (certificate->round cert) round))
             (cert-with-author+round author round certs))
    :induct t
    :enable head-when-certificate-setp)

  (defruled cert-with-author+round-when-subset
    (implies (and (cert-with-author+round author round certs0)
                  (set::subset certs0 certs)
                  (certificate-setp certs))
             (cert-with-author+round author round certs))
    :use (:instance cert-with-author+round-when-element
                    (author (address-fix author))
                    (round (pos-fix round))
                    (cert (cert-with-author+round author round certs0)))
    :enable (cert-with-author+round-element
             set::expensive-rules)
    :disable cert-with-author+round)

  (defruled cert-with-author+round-of-insert-iff
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (iff (cert-with-author+round
                   author round (set::insert cert certs))
                  (or (and (equal (certificate->author cert)
                                  (address-fix author))
                           (equal (certificate->round cert)
                                  (pos-fix round)))
                      (cert-with-author+round author round certs))))
    :use (only-if-part if-part)

    :prep-lemmas

    ((local (in-theory (disable cert-with-author+round)))

     (defruled only-if-part
       (implies (and (certificatep cert)
                     (certificate-setp certs)
                     (or (not (equal (certificate->author cert)
                                     (address-fix author)))
                         (not (equal (certificate->round cert)
                                     (pos-fix round))))
                     (cert-with-author+round author
                                             round
                                             (set::insert cert certs)))
                (cert-with-author+round author round certs))
       :use ((:instance cert-with-author+round-element
                        (certs (set::insert cert certs)))
             (:instance cert-with-author+round-when-element
                        (author (address-fix author))
                        (round (pos-fix round))
                        (cert (cert-with-author+round
                               author round (set::insert cert certs))))))

     (defruled if-part
       (implies (and (certificatep cert)
                     (certificate-setp certs)
                     (or (and (equal (certificate->author cert)
                                     (address-fix author))
                              (equal (certificate->round cert)
                                     (pos-fix round)))
                         (cert-with-author+round author round certs)))
                (cert-with-author+round author
                                        round
                                        (set::insert cert certs)))
       :enable cert-with-author+round-when-subset
       :use (:instance cert-with-author+round-when-element
                       (author (address-fix author))
                       (round (pos-fix round))
                       (certs (set::insert cert certs))))))

  (defruled cert-with-author+round-of-union-iff
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (iff (cert-with-author+round
                   author round (set::union certs1 certs2))
                  (or (cert-with-author+round author round certs1)
                      (cert-with-author+round author round certs2))))
    :induct t
    :enable (set::union
             cert-with-author+round-of-insert-iff
             head-when-certificate-setp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-author ((author addressp) (certs certificate-setp))
  :returns (certs-with-author certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given author."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       ((certificate cert) (set::head certs)))
    (if (equal cert.author (address-fix author))
        (set::insert cert
                     (certs-with-author author (set::tail certs)))
      (certs-with-author author (set::tail certs))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret certs-with-author-subset
    (set::subset certs-with-author certs)
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))

  (defruled in-of-certs-with-author
    (equal (set::in cert (certs-with-author author certs))
           (and (set::in cert (certificate-set-fix certs))
                (equal (certificate->author cert)
                       (address-fix author))))
    :induct t)

  (defrule certs-with-author-of-empty
    (equal (certs-with-author author nil) nil))

  (defruled certificate-with-author-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certs-with-author author
                                       (set::insert cert certs))
                    (if (equal (certificate->author cert)
                               (address-fix author))
                        (set::insert cert
                                     (certs-with-author author certs))
                      (certs-with-author author certs))))
    :enable (in-of-certs-with-author
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable certs-with-author)

  (defruled certificate-with-author-of-delete
    (implies (certificate-setp certs)
             (equal (certs-with-author author
                                       (set::delete cert certs))
                    (set::delete cert
                                 (certs-with-author author certs))))
    :enable (in-of-certs-with-author
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable certs-with-author)

  (defruled certs-with-author-of-intersect
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (certs-with-author author
                                       (set::intersect certs1 certs2))
                    (set::intersect
                     (certs-with-author author certs1)
                     (certs-with-author author certs2))))
    :enable (in-of-certs-with-author
             set::expensive-rules
             set::double-containment-no-backchain-limit)
    :disable certs-with-author)

  (defruled cert-set->author-set-of-certs-with-author
    (implies (certificate-setp certs)
             (equal (cert-set->author-set
                     (certs-with-author author certs))
                    (if (set::in (address-fix author)
                                 (cert-set->author-set certs))
                        (set::insert (address-fix author) nil)
                      nil)))
    :induct t
    :enable (cert-set->author-set
             cert-set->author-set-of-insert))

  (defruled emptyp-of-certs-with-author-if-no-author
    (implies (certificate-setp certs)
             (equal (set::emptyp (certs-with-author author certs))
                    (not (set::in (address-fix author)
                                  (cert-set->author-set certs)))))
    :induct t
    :enable cert-set->author-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-round ((round posp)
                          (certs certificate-setp))
  :returns (certs-with-round certificate-setp)
  :short "Retrieve the set of certificates with a given round from a set."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (equal round cert.round)
        (set::insert (certificate-fix cert)
                     (certs-with-round round (set::tail certs)))
      (certs-with-round round (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret certs-with-round-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-round certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* in-of-certs-with-author
                                 set::subset
                                 set::expensive-rules))))
  (in-theory (disable certs-with-round-subset))

  (defruled in-of-certs-with-round
    (implies (certificate-setp certs)
             (equal (set::in cert (certs-with-round round certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert) round))))
    :induct t)

  (defruled certs-with-round-when-emptyp
    (implies (set::emptyp certs)
             (equal (certs-with-round round certs)
                    nil)))

  (defruled certs-with-round-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certs-with-round round
                                      (set::insert cert certs))
                    (if (equal (certificate->round cert) round)
                        (set::insert cert
                                     (certs-with-round round
                                                       certs))
                      (certs-with-round round certs))))
    :induct (set::weak-insert-induction cert certs)
    :enable in-of-certs-with-round)

  (defruled certs-with-round-monotone
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (set::subset certs1 certs2))
             (set::subset (certs-with-round round certs1)
                          (certs-with-round round certs2)))
    :enable (set::expensive-rules
             in-of-certs-with-round))

  (defruled cert-with-author+round-when-author-in-round
    (implies (and (certificate-setp certs)
                  (set::in author
                           (cert-set->author-set
                            (certs-with-round round certs))))
             (cert-with-author+round author round certs))
    :use (:instance set::in-head
                    (x (certs-with-author
                        author (certs-with-round round certs))))
    :enable (set::expensive-rules
             in-of-certs-with-author
             in-of-certs-with-round
             cert-with-author+round-when-element
             emptyp-of-certs-with-author-if-no-author)
    :disable set::in-head)

  (defruled certs-with-round-of-intersect
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2))
             (equal (certs-with-round
                     round (set::intersect certs1 certs2))
                    (set::intersect
                     (certs-with-round round certs1)
                     (certs-with-round round certs2))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certs-with-round))

  (defruled round-set-of-certs-with-round
    (equal (cert-set->round-set
            (certs-with-round round certs))
           (if (set::emptyp (certs-with-round round certs))
               nil
             (set::insert round nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled round-set-of-certs-with-round-possibilities
    (or (equal (cert-set->round-set
                (certs-with-round round certs))
               nil)
        (equal (cert-set->round-set
                (certs-with-round round certs))
               (set::insert round nil)))
    :induct t
    :enable (cert-set->round-set
             cert-set->round-set-of-insert))

  (defruled cardinality-of-round-set-of-certs-with-round
    (<= (set::cardinality
         (cert-set->round-set
          (certs-with-round round certs)))
        1)
    :rule-classes :linear
    :use round-set-of-certs-with-round-possibilities
    :enable set::cardinality)

  (defruled cardinality-of-subset-of-round-set-of-round
    (implies (set::subset certs0
                          (certs-with-round round certs))
             (<= (set::cardinality
                  (cert-set->round-set certs0))
                 1))
    :rule-classes :linear
    :enable (cardinality-of-round-set-of-certs-with-round
             cert-set->round-set-monotone)
    :use ((:instance set::subset-cardinality
                     (x (cert-set->round-set certs0))
                     (y (cert-set->round-set
                         (certs-with-round round certs)))))
    :disable set::subset-cardinality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-authors ((authors address-setp)
                            (certs certificate-setp))
  :returns (certs-with-authors certificate-setp)
  :short "Retrieve the set of certificates with given authors from a set."
  (cond ((set::emptyp authors) nil)
        (t (set::union
            (certs-with-author (set::head authors) certs)
            (certs-with-authors (set::tail authors) certs))))
  :verify-guards :after-returns
  ///

  (defret certs-with-authors-subset
    (implies (certificate-setp certs)
             (set::subset certs-with-authors certs))
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))
  (in-theory (disable certs-with-authors-subset))

  (defruled in-of-certs-with-authors
    (implies (and (certificate-setp certs)
                  (address-setp authors))
             (equal (set::in cert
                             (certs-with-authors authors certs))
                    (and (set::in cert certs)
                         (set::in (certificate->author cert) authors))))
    :induct t
    :enable in-of-certs-with-author
    :hints ('(:use (:instance set::in-tail-or-head
                              (a (certificate->author cert))
                              (x authors)))))

  (defruled author-set-of-certs-with-authors
    (implies (and (address-setp authors)
                  (certificate-setp certs))
             (equal (cert-set->author-set
                     (certs-with-authors authors certs))
                    (set::intersect authors
                                    (cert-set->author-set certs))))
    :induct t
    :enable (cert-set->author-set
             set::expensive-rules
             cert-set->author-set-of-certs-with-author
             cert-set->author-set-of-union)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-authors+round ((authors address-setp)
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
                     (certs-with-authors+round authors
                                               round
                                               (set::tail certs)))
      (certs-with-authors+round authors
                                round
                                (set::tail certs))))
  :verify-guards :after-returns
  ///

  (defret certs-with-authors+round-subset
    (set::subset certs-with-authors-and-round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))
  (in-theory (disable certs-with-authors+round-subset))

  (defruled certificates-authors-of-certs-with-authors+round-subset
    (b* ((returned-authors
          (cert-set->author-set
           (certs-with-authors+round authors round certs))))
      (set::subset returned-authors authors))
    :induct t
    :enable cert-set->author-set-of-insert)

  (defruled round-set-of-certs-with-authors+round
    (equal (cert-set->round-set
            (certs-with-authors+round authors round certs))
           (if (set::emptyp
                (certs-with-authors+round authors round certs))
               nil
             (set::insert round nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled cert-set->round-set-of-certs-with-authors+round
    (b* ((rounds (cert-set->round-set
                  (certs-with-authors+round authors round certs))))
      (implies (not (set::emptyp rounds))
               (equal rounds
                      (set::insert (pos-fix round) nil))))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled in-of-certs-with-authors+round
    (implies (certificate-setp certs)
             (equal (set::in cert
                             (certs-with-authors+round authors
                                                       round
                                                       certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert) round)
                         (set::in (certificate->author cert) authors))))
    :induct t)

  (defret certs-with-authors+round-subset-with-round
    (set::subset certs-with-authors-and-round
                 (certs-with-round round certs))
    :hyp (certificate-setp certs)
    :hints
    (("Goal" :in-theory (enable* set::expensive-rules
                                 in-of-certs-with-round
                                 in-of-certs-with-authors+round))))
  (in-theory (disable certs-with-authors+round-subset-with-round))

  (defruled certs-with-authors+round-of-empty-authors
    (implies (set::emptyp authors)
             (equal (certs-with-authors+round authors round certs)
                    nil))
    :induct t)

  (defruled certs-with-authors+round-to-authors-of-round
    (implies (and (certificate-setp certs)
                  (address-setp authors))
             (equal (certs-with-authors+round authors round certs)
                    (certs-with-authors
                     authors (certs-with-round round certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certs-with-round
             in-of-certs-with-authors
             in-of-certs-with-authors+round))

  (defruled certs-with-authors+round-to-round-of-authors
    (implies (and (certificate-setp certs)
                  (address-setp authors))
             (equal (certs-with-authors+round authors round certs)
                    (certs-with-round
                     round (certs-with-authors authors certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certs-with-round
             in-of-certs-with-authors
             in-of-certs-with-authors+round)))
