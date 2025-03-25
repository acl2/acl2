; AleoBFT Library
;
; Copyright (C) 2025 Provable Inc.
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
  (cond ((set::emptyp certs) nil)
        (t (set::insert (certificate->author (set::head certs))
                        (cert-set->author-set (set::tail certs)))))
  :verify-guards :after-returns
  ///

  (defruled certificate->author-in-cert-set->author-set
    (implies (set::in cert certs)
             (set::in (certificate->author cert)
                      (cert-set->author-set certs)))
    :induct t)

  (defruled cert-set->author-set-of-insert
    (equal (cert-set->author-set (set::insert cert certs))
           (set::insert (certificate->author cert)
                        (cert-set->author-set certs)))
    :induct t
    :enable (set::in
             certificate->author-in-cert-set->author-set))

  (defruled cert-set->author-set-of-union
    (equal (cert-set->author-set (set::union certs1 certs2))
           (set::union (cert-set->author-set certs1)
                       (cert-set->author-set (set::sfix certs2))))
    :induct t
    :enable (set::union
             cert-set->author-set-of-insert))

  (defruled emptyp-of-cert-set->author-set
    (equal (set::emptyp (cert-set->author-set certs))
           (set::emptyp certs))
    :induct t)

  (defruled cert-set->author-set-monotone
    (implies (set::subset certs1 certs2)
             (set::subset (cert-set->author-set certs1)
                          (cert-set->author-set certs2)))
    :induct t
    :enable (set::subset
             certificate->author-in-cert-set->author-set))

  (defruled same-certificate-author-when-cardinality-leq-1
    (implies (and (<= (set::cardinality (cert-set->author-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
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
  (cond ((set::emptyp certs) nil)
        (t (set::insert (certificate->round (set::head certs))
                        (cert-set->round-set (set::tail certs)))))
  :verify-guards :after-returns
  ///

  (defruled certificate->round-in-cert-set->round-set
    (implies (set::in cert certs)
             (set::in (certificate->round cert)
                      (cert-set->round-set certs)))
    :induct t)

  (defruled cert-set->round-set-of-insert
    (equal (cert-set->round-set (set::insert cert certs))
           (set::insert (certificate->round cert)
                        (cert-set->round-set certs)))
    :induct t
    :enable (set::in
             certificate->round-in-cert-set->round-set))

  (defruled cert-set->round-set-of-union
    (equal (cert-set->round-set (set::union certs1 certs2))
           (set::union (cert-set->round-set certs1)
                       (cert-set->round-set (set::sfix certs2))))
    :induct t
    :enable (set::union
             cert-set->round-set-of-insert))

  (defruled emptyp-of-cert-set->round-set
    (equal (set::emptyp (cert-set->round-set certs))
           (set::emptyp certs))
    :induct t)

  (defruled cert-set->round-set-monotone
    (implies (set::subset certs1 certs2)
             (set::subset (cert-set->round-set certs1)
                          (cert-set->round-set certs2)))
    :induct t
    :enable (set::subset
             certificate->round-in-cert-set->round-set))

  (defruled same-certificate-round-when-cardinality-leq-1
    (implies (and (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
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
    :enable (certificate-with-author+round-when-subset
             certificate->author-of-certificate-with-author+round))

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
    (set::subset certs-with-author certs)
    :hyp (certificate-setp certs)
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

  (defruled cert-set->author-set-of-certificates-with-author
    (implies (certificate-setp certs)
             (equal (cert-set->author-set
                     (certificates-with-author author certs))
                    (if (set::in (address-fix author)
                                 (cert-set->author-set certs))
                        (set::insert (address-fix author) nil)
                      nil)))
    :induct t
    :enable (cert-set->author-set
             cert-set->author-set-of-insert))

  (defruled in-cert-set->author-set-to-nonempty-certs-with-author
    (implies (certificate-setp certs)
             (equal (set::in author (cert-set->author-set certs))
                    (and (addressp author)
                         (not (set::emptyp
                               (certificates-with-author author certs))))))
    :induct t
    :enable cert-set->author-set)

  (defruled certificates-with-author-when-emptyp
    (implies (set::emptyp certs)
             (equal (certificates-with-author author certs)
                    nil)))

  (defruled certificates-with-author-of-insert
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

  (defruled certificates-with-author-of-delete
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
             certificate-with-author+round-element
             certificate->author-of-certificate-with-author+round)
    :disable certificates-with-author)

  (defruled no-certificate-with-author+round-if-no-certificates-with-author
    (implies (and (certificate-setp certs)
                  (equal (certificates-with-author author certs)
                         nil))
             (not (certificate-with-author+round author round certs)))
    :use certificate-with-author+round-in-certificates-with-author
    :disable certificates-with-author)

  (defruled emptyp-of-certificates-with-author-if-no-author
    (equal (set::emptyp (certificates-with-author author certs))
           (not (set::in (address-fix author)
                         (cert-set->author-set certs))))
    :induct t
    :enable cert-set->author-set))

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
    (set::subset certs-with-round certs)
    :hyp (certificate-setp certs)
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
    :disable certificates-with-round)

  (defruled cert-set->round-set-of-certificates-with-round
    (equal (cert-set->round-set
            (certificates-with-round round certs))
           (if (set::in (pos-fix round)
                        (cert-set->round-set certs))
               (set::insert (pos-fix round) nil)
             nil))
    :induct t
    :enable (cert-set->round-set
             cert-set->round-set-of-insert))

  (defruled emptyp-of-certificates-with-round-to-no-round
    (equal (set::emptyp (certificates-with-round round certs))
           (not (set::in (pos-fix round)
                         (cert-set->round-set certs))))
    :induct t
    :enable cert-set->round-set)

  (defruled cardinality-of-round-set-of-certificates-with-round
    (<= (set::cardinality
         (cert-set->round-set
          (certificates-with-round round certs)))
        1)
    :rule-classes :linear
    :enable (cert-set->round-set-of-certificates-with-round
             set::cardinality)
    :disable certificates-with-round)

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
    :disable (set::subset-cardinality
              certificates-with-round))

  (defruled certificate-with-author+round-when-author-in-round
    (implies (and (certificate-setp certs)
                  (posp round)
                  (set::in author
                           (cert-set->author-set
                            (certificates-with-round round certs))))
             (certificate-with-author+round author round certs))
    :use (:instance set::in-head
                    (x (certificates-with-author
                        author (certificates-with-round round certs))))
    :enable (in-of-certificates-with-author
             in-of-certificates-with-round
             certificate-with-author+round-when-element
             emptyp-of-certificates-with-author-if-no-author)
    :disable (set::in-head
              certificates-with-round)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificates-with-authors ((authors address-setp)
                                   (certs certificate-setp))
  :returns (certs-with-authors certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with author in a given set."
  (b* (((when (set::emptyp certs)) nil)
       ((certificate cert) (set::head certs)))
    (if (set::in cert.author
                 (address-set-fix authors))
        (set::insert (certificate-fix cert)
                     (certificates-with-authors authors (set::tail certs)))
      (certificates-with-authors authors (set::tail certs))))
  :verify-guards :after-returns
  ///

  (fty::deffixequiv certificates-with-authors
    :args ((authors address-setp)))

  (defret certificates-with-authors-subset
    (set::subset certs-with-authors certs)
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))
  (in-theory (disable certificates-with-authors-subset))

  (defruled in-of-certificates-with-authors
    (implies (certificate-setp certs)
             (equal (set::in cert (certificates-with-authors authors certs))
                    (and (set::in cert certs)
                         (set::in (certificate->author cert)
                                  (address-set-fix authors)))))
    :induct t)

  (defruled cert-set->author-set-of-certificates-with-authors
    (equal (cert-set->author-set
            (certificates-with-authors authors certs))
           (set::intersect (address-set-fix authors)
                           (cert-set->author-set certs)))
    :induct t
    :enable (cert-set->author-set
             cert-set->author-set-of-insert
             set::expensive-rules)))

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
    (if (and (set::in cert.author
                      (address-set-fix authors))
             (equal cert.round
                    (pos-fix round)))
        (set::insert (certificate-fix cert)
                     (certificates-with-authors+round authors
                                                      round
                                                      (set::tail certs)))
      (certificates-with-authors+round authors
                                       round
                                       (set::tail certs))))
  :verify-guards :after-returns

  ///

  (fty::deffixequiv certificates-with-authors+round
    :args ((authors address-setp) (round posp)))

  (defret certificates-with-authors+round-subset
    (set::subset certs-with-authors-and-round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :induct t
             :in-theory (enable* set::subset
                                 set::expensive-rules))))
  (in-theory (disable certificates-with-authors+round-subset))

  (defruled in-of-certificates-with-authors+round
    (implies (certificate-setp certs)
             (equal (set::in cert
                             (certificates-with-authors+round authors
                                                              round
                                                              certs))
                    (and (set::in cert certs)
                         (equal (certificate->round cert)
                                (pos-fix round))
                         (set::in (certificate->author cert)
                                  (address-set-fix authors)))))
    :induct t)

  (defruled certificates-with-authors+round-when-emptyp
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
             in-of-certificates-with-authors+round
             in-of-certificates-with-authors
             in-of-certificates-with-round)
    :disable certificates-with-authors+round)

  (defruled certificates-with-authors+round-to-round-of-authors
    (implies (certificate-setp certs)
             (equal (certificates-with-authors+round authors round certs)
                    (certificates-with-round
                     round (certificates-with-authors authors certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certificates-with-authors+round
             in-of-certificates-with-authors
             in-of-certificates-with-round)
    :disable certificates-with-authors+round)

  (defruled cert-set->round-set-of-certificates-with-authors+round
    (equal (cert-set->round-set
            (certificates-with-authors+round authors round certs))
           (if (set::emptyp
                (certificates-with-authors+round authors round certs))
               nil
             (set::insert (pos-fix round) nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled
    cert-set->round-set-of-certificates-with-authors+round-not-empty
    (b* ((rounds (cert-set->round-set
                  (certificates-with-authors+round authors round certs))))
      (implies (not (set::emptyp rounds))
               (equal rounds
                      (set::insert (pos-fix round) nil))))
    :induct t
    :enable cert-set->round-set-of-insert))

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
     the added certificate's author and round.")
   (xdoc::p
    "The theorem @('equal-certificate-authors-when-unequiv-and-same-round')
     says that if the certificates in an unequivocal sets
     have all the same round,
     then two certificates in that set are the same
     if they have the same author.
     We phrase it as a rewrite rule
     in the typical form of an injectivity rewrite rule.")
   (xdoc::p
    "The theorem
     @('head-author-not-in-tail-authors-when-unequiv-and-all-same-round')
     is mainly a consequence of the previous one,
     considering the first certificate in a set
     and a generic one in the rest of the set.")
   (xdoc::p
    "The previous theorem is used to prove
     @('cardinality-of-authors-when-unequiv-and-all-same-rounds'),
     which says that the number of authors
     of a set of certificates all in the same round
     is the same as the number of those certificates:
     unequivocation means that there is a bijection between
     those authors and those certificates.")
   (xdoc::p
    "The previous theorem is used to prove
     @('cardinality-of-certificates-with-authors+round-when-subset'),
     which in a sense specializes the previous one to
     the certificates returned by @(tsee certificates-with-authors+round).
     Note that this returns certificates all in the same round,
     so they are in bijection with their authors,
     given that the certificates are unequivocal."))
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
       :enable (certificate-with-author+round-element
                certificate->author-of-certificate-with-author+round
                certificate->round-of-certificate-with-author+round))))

  (defruled equal-certificate-authors-when-unequiv-and-same-round
    (implies (and (certificate-set-unequivocalp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
             (equal (equal (certificate->author cert1)
                           (certificate->author cert2))
                    (equal cert1 cert2)))
    :use (certificate-set-unequivocalp-necc
          same-certificate-round-when-cardinality-leq-1)
    :disable (certificate-set-unequivocalp
              certificate-set-unequivocalp-necc))

  (defruled head-author-not-in-tail-authors-when-unequiv-and-all-same-round
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (not (set::emptyp certs)))
             (not (set::in (certificate->author (set::head certs))
                           (cert-set->author-set (set::tail certs)))))
    :use ((:instance set::in-head
                     (x (certificates-with-author
                         (certificate->author (head certs))
                         (tail certs))))
          (:instance set::in-head
                     (x certs)))
    :enable (certificates-with-author-subset
             in-of-certificates-with-author
             emptyp-of-certificates-with-author-if-no-author
             equal-certificate-authors-when-unequiv-and-same-round)
    :disable (set::in-head
              certificate-set-unequivocalp
              certificate-set-unequivocalp-necc))

  (defruled cardinality-of-authors-when-unequiv-and-all-same-rounds
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1))
             (equal (set::cardinality (cert-set->author-set certs))
                    (set::cardinality certs)))
    :induct t
    :enable (set::cardinality
             cert-set->author-set
             head-author-not-in-tail-authors-when-unequiv-and-all-same-round
             certificate-set-unequivocalp-when-subset
             set::expensive-rules)
    :disable (cert-set->round-set-monotone
              certificate-set-unequivocalp
              certificate-set-unequivocalp-necc)
    :hints ('(:use (:instance cert-set->round-set-monotone
                              (certs1 (set::tail certs))
                              (certs2 certs)))))

  (defruled cardinality-of-certificates-with-authors+round-when-subset
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (set::subset (address-set-fix authors)
                               (cert-set->author-set
                                (certificates-with-round round certs))))
             (equal (set::cardinality
                     (certificates-with-authors+round authors round certs))
                    (set::cardinality (address-set-fix authors))))
    :use ((:instance cardinality-of-authors-when-unequiv-and-all-same-rounds
                     (certs
                      (certificates-with-authors+round authors round certs)))
          (:instance cardinality-of-subset-of-round-set-of-round
                     (certs0 (certificates-with-authors
                              authors
                              (certificates-with-round round certs))))
          (:instance set::subset-transitive
                     (x (certificates-with-authors
                         authors (certificates-with-round round certs)))
                     (y (certificates-with-round round certs))
                     (z certs)))
    :enable (certificates-with-authors+round-to-authors-of-round
             cert-set->author-set-of-certificates-with-authors
             certificates-with-authors-subset
             certificates-with-round-subset
             certificate-set-unequivocalp-when-subset)
    :disable (set::subset-transitive
              certificate-set-unequivocalp
              certificate-set-unequivocalp-necc)))

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
     but the non-equivocation of the second set prevents that.")
   (xdoc::p
    "The theorem @('certificate-set-unequivocalp-of-union')
     says that given two sets of certificates
     that are individually and jointly unequivocal,
     their union is unequivocal.
     This is is easy to prove by cases of
     where the two witness certificates come from."))
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
       :enable (certificate-with-author+round-element
                certificate->author-of-certificate-with-author+round
                certificate->round-of-certificate-with-author+round))))

  (defruled certificate-set-unequivocalp-of-union
    (implies (and (certificate-set-unequivocalp certs1)
                  (certificate-set-unequivocalp certs2)
                  (certificate-sets-unequivocalp certs1 certs2))
             (certificate-set-unequivocalp (set::union certs1 certs2)))
    :enable (certificate-set-unequivocalp
             set::expensive-rules)
    :disable certificate-sets-unequivocalp
    :use ((:instance certificate-set-unequivocalp-necc
                     (cert1 (mv-nth 0 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))
                     (cert2 (mv-nth 1 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))
                     (certs certs1))
          (:instance certificate-set-unequivocalp-necc
                     (cert1 (mv-nth 0 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))
                     (cert2 (mv-nth 1 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))
                     (certs certs2))
          (:instance certificate-sets-unequivocalp-necc
                     (cert1 (mv-nth 0 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))
                     (cert2 (mv-nth 1 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2)))))
          (:instance certificate-sets-unequivocalp-necc
                     (cert1 (mv-nth 1 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))
                     (cert2 (mv-nth 0 (certificate-set-unequivocalp-witness
                                       (union certs1 certs2))))))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-certificate-with-author+round
  :short "Properties of @(tsee certificate-with-author+round)
          when used on unequivocal certificate sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     if a certificate is in an unequivocal set,
     retrieving a certificate with the certificate's author and round
     will return the certificate itself.
     This is not the case unless the set is unequivocal:
     there could be multiple certificates with the same author and round,
     and the operation may not return the specific @('cert').")
   (xdoc::p
    "The second theorem says that
     if a certificate with a certain author and round
     is retrieved from a subset of an unequivocal set of certificates,
     the same certificate is retrieved from the superset.
     Note that the subset is also unequivocal,
     but that is a consequence of the superset being unequivocal.")
   (xdoc::p
    "The third theorem says that
     if a certificate with a certain author and round
     is retrieved from both of two mutually unequivocal certificate sets,
     it is the same certificate from both sets."))

  (defruled certificate-with-author+round-of-element-when-unequivocal
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (set::in cert certs))
             (equal (certificate-with-author+round (certificate->author cert)
                                                   (certificate->round cert)
                                                   certs)
                    cert))
    :enable (certificate-with-author+round-element
             certificate-with-author+round-when-element
             certificate->author-of-certificate-with-author+round
             certificate->round-of-certificate-with-author+round)
    :use (:instance certificate-set-unequivocalp-necc
                    (cert1 cert)
                    (cert2 (certificate-with-author+round
                            (certificate->author cert)
                            (certificate->round cert)
                            certs))))

  (defruled certificate-with-author+round-of-unequivocal-superset
    (implies (and (certificate-setp certs0)
                  (certificate-setp certs)
                  (set::subset certs0 certs)
                  (certificate-set-unequivocalp certs)
                  (certificate-with-author+round author round certs0))
             (equal (certificate-with-author+round author round certs)
                    (certificate-with-author+round author round certs0)))
    :use (:instance certificate-set-unequivocalp-necc
                    (cert1
                     (certificate-with-author+round author round certs0))
                    (cert2
                     (certificate-with-author+round author round certs)))
    :enable (certificate-with-author+round-when-subset
             certificate-with-author+round-element
             certificate->author-of-certificate-with-author+round
             certificate->round-of-certificate-with-author+round
             set::expensive-rules))

  (defruled certificate-with-author+round-of-unequivocal-sets
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (certificate-sets-unequivocalp certs1 certs2)
                  (certificate-with-author+round author round certs1)
                  (certificate-with-author+round author round certs2))
             (equal (certificate-with-author+round author round certs1)
                    (certificate-with-author+round author round certs2)))
    :enable (certificate-with-author+round-element
             certificate->author-of-certificate-with-author+round
             certificate->round-of-certificate-with-author+round)
    :use (:instance
          certificate-sets-unequivocalp-necc
          (cert1 (certificate-with-author+round author round certs1))
          (cert2 (certificate-with-author+round author round certs2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection unequivocal-certificates-with-authors+round
  :short "Properties of @(tsee certificates-with-authors+round)
          when used on unequivocal certificate sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem says that
     if certificates with certain authors and a certain round
     are retrieved from a subset of an unequivocal set of certificates,
     the same certificates are retrieved from the superset.
     Note the hypothesis that the given authors are
     all in the certificates at the given round in the subset.
     That is, a certificates for each author is in the subset at the round.
     Otherwise, the superset could have additional certificates at the round,
     with authors not found in the subset at the round.
     For the proof, we introduce a local lemma for
     the membership subgoal that arises
     from the pick-a-point strategy.")
   (xdoc::p
    "The second theorem says that
     if certificates with certain authors and a certain round
     are retrieved from both of two mutually unequivocal certificate sets,
     the same certificates are retrieved from both sets.
     For the proof, we introduce two local lemmas for
     the two containment membership subgoals
     from the pick-a-point strategy.
     The first hypothesis of the first lemma binds
     the @('authors') and @('certs1') variables;
     the first hypothesis of the second lemma binds
     the @('authors') and @('certs2') variables."))

  (defruled certificates-with-authors+round-of-unequivocal-superset
    (implies (and (certificate-setp certs0)
                  (certificate-setp certs)
                  (set::subset certs0 certs)
                  (certificate-set-unequivocalp certs)
                  (posp round)
                  (address-setp authors)
                  (set::subset authors
                               (cert-set->author-set
                                (certificates-with-round round certs0))))
             (equal (certificates-with-authors+round authors round certs)
                    (certificates-with-authors+round authors round certs0)))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             certificate-with-author+round-when-author-in-round
             in-of-certificates-with-authors+round)
    :prep-lemmas
    ((defrule lemma
       (implies (and (certificate-setp certs0)
                     (certificate-setp certs)
                     (set::subset certs0 certs)
                     (certificate-set-unequivocalp certs)
                     (set::in cert certs)
                     (certificate-with-author+round (certificate->author cert)
                                                    (certificate->round cert)
                                                    certs0))
                (set::in cert certs0))
       :use (:instance certificate-set-unequivocalp-necc
                       (cert1 cert)
                       (cert2 (certificate-with-author+round
                               (certificate->author cert)
                               (certificate->round cert)
                               certs0)))
       :enable (set::expensive-rules
                certificate-with-author+round-element
                certificate->author-of-certificate-with-author+round
                certificate->round-of-certificate-with-author+round))))

  (defruled certificates-with-authors+round-of-unequivocal-sets
    (implies (and (certificate-setp certs1)
                  (certificate-setp certs2)
                  (certificate-sets-unequivocalp certs1 certs2)
                  (posp round)
                  (address-setp authors)
                  (set::subset authors
                               (cert-set->author-set
                                (certificates-with-round round certs1)))
                  (set::subset authors
                               (cert-set->author-set
                                (certificates-with-round round certs2))))
             (equal (certificates-with-authors+round authors round certs1)
                    (certificates-with-authors+round authors round certs2)))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certificates-with-authors+round)
    :prep-lemmas
    ((defrule lemma1
       (implies (and ; binds authors & certs1
                 (set::subset authors
                              (cert-set->author-set
                               (certificates-with-round
                                (certificate->round cert) certs1)))
                 (certificate-setp certs1)
                 (certificate-setp certs2)
                 (certificate-sets-unequivocalp certs1 certs2)
                 (set::in cert certs1)
                 (set::in (certificate->author cert) authors)
                 (set::subset authors
                              (cert-set->author-set
                               (certificates-with-round
                                (certificate->round cert) certs2))))
                (set::in cert certs2))
       :use ((:instance certificate-with-author+round-element
                        (certs certs2)
                        (author (certificate->author cert))
                        (round (certificate->round cert)))
             (:instance certificate-sets-unequivocalp-necc
                        (cert1 cert)
                        (cert2 (certificate-with-author+round
                                (certificate->author cert)
                                (certificate->round cert)
                                certs2))))
       :enable (set::expensive-rules
                certificate-with-author+round-when-author-in-round
                certificate->author-of-certificate-with-author+round
                certificate->round-of-certificate-with-author+round))
     (defrule lemma2
       (implies (and ; binds authors & certs2
                 (set::subset authors
                              (cert-set->author-set
                               (certificates-with-round
                                (certificate->round cert) certs2)))
                 (certificate-setp certs1)
                 (certificate-setp certs2)
                 (certificate-sets-unequivocalp certs1 certs2)
                 (set::in cert certs2)
                 (set::in (certificate->author cert) authors)
                 (set::subset authors
                              (cert-set->author-set
                               (certificates-with-round
                                (certificate->round cert) certs1))))
                (set::in cert certs1))
       :use ((:instance certificate-with-author+round-element
                        (certs certs1)
                        (author (certificate->author cert))
                        (round (certificate->round cert)))
             (:instance certificate-sets-unequivocalp-necc
                        (cert1 (certificate-with-author+round
                                (certificate->author cert)
                                (certificate->round cert)
                                certs1))
                        (cert2 cert)))
       :enable (set::expensive-rules
                certificate-with-author+round-when-author-in-round
                certificate->author-of-certificate-with-author+round
                certificate->round-of-certificate-with-author+round)))))
