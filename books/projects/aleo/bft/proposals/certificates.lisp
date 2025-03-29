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

(include-book "proposals")

(include-book "kestrel/fty/pos-set" :dir :system)

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
     which consist of proposals with endorsing signatures.
     Certificates are the vertices of the DAG,
     in the Narwhal part of AleoBFT.")
   (xdoc::p
    "Beside defining certificates,
     we also introduce operations on (sets of) certificates,
     particularly to retrieve certificates from sets
     according to author and/or round criteria.
     Since DAGs are represented as sets in validator states,
     these operations are usable (and in fact mainly used) on DAGs."))
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
     "A proposal.")
    (xdoc::li
     "The addresses of the validators that endorsed the proposal,
      by signing it in addition to the author."))
   (xdoc::p
    "We do not model cryptographic signatures explicitly.
     The presence of an endorser address in a certificate
     models the fact that the validator with that address
     endorsed the proposal by signing it."))
  ((proposal proposal)
   (endorsers address-set))
  :pred certificatep)

;;;;;;;;;;;;;;;;;;;;

(define certificate->author ((cert certificatep))
  :returns (author addressp)
  :short "Author of (the proposal in) a certificate."
  (proposal->author (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define certificate->round ((cert certificatep))
  :returns (round posp)
  :short "Round number of (the proposal in) a certificate."
  (proposal->round (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define certificate->transactions ((cert certificatep))
  :returns (transactions transaction-listp)
  :short "List of transactions of (the proposal in) a certificate."
  (proposal->transactions (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define certificate->previous ((cert certificatep))
  :returns (previous address-setp)
  :short "Set of references to previous certificates
          of (the proposal in) a certificate."
  (proposal->previous (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define certificate->signers ((cert certificatep))
  :returns (signers address-setp)
  :short "Signers of a certificate."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the author and the endorsers,
     i.e. all the validators who signed the certificate."))
  (set::insert (certificate->author cert)
               (certificate->endorsers cert))
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
  :pred certificate-setp)

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
    (implies (and (certificate-setp certs)
                  (set::in cert certs))
             (set::in (certificate->author cert)
                      (cert-set->author-set certs)))
    :induct t)

  (defruled cert-set->author-set-monotone
    (implies (and (certificate-setp certs2)
                  (set::subset certs1 certs2))
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
    :enable certificate->author-in-cert-set->author-set))

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
    (implies (and (certificate-setp certs)
                  (set::in cert certs))
             (set::in (certificate->round cert)
                      (cert-set->round-set certs)))
    :induct t)

  (defruled cert-set->round-set-monotone
    (implies (and (certificate-setp certs2)
                  (set::subset certs1 certs2))
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
    :enable certificate->round-in-cert-set->round-set))

;;;;;;;;;;;;;;;;;;;;

(define cert-set->prop-set ((certs certificate-setp))
  :returns (props proposal-setp)
  :short "Lift @(tsee certificate->proposal) to sets."
  (cond ((set::emptyp (certificate-set-fix certs)) nil)
        (t (set::insert (certificate->proposal (set::head certs))
                        (cert-set->prop-set (set::tail certs)))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule emptyp-of-cert-set->prop-set
    (equal (set::emptyp (cert-set->prop-set certs))
           (set::emptyp (certificate-set-fix certs)))
    :induct t)

  (defruled certificate->proposal-in-cert-set->prop-set
    (implies (and (certificate-setp certs)
                  (set::in cert certs))
             (set::in (certificate->proposal cert)
                      (cert-set->prop-set certs)))
    :induct t)

  (defruled cert-set->prop-set-monotone
    (implies (and (certificate-setp certs2)
                  (set::subset certs1 certs2))
             (set::subset (cert-set->prop-set certs1)
                          (cert-set->prop-set certs2)))
    :induct t
    :enable (set::subset
             certificate->proposal-in-cert-set->prop-set))

  (defruled cert-set->prop-set-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (cert-set->prop-set (set::insert cert certs))
                    (set::insert (certificate->proposal cert)
                                 (cert-set->prop-set certs))))
    :induct (set::weak-insert-induction cert certs)
    :enable certificate->proposal-in-cert-set->prop-set))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist certificate-list
  :short "Fixtype of lists of certificates."
  :elt-type certificate
  :true-listp t
  :elementp-of-nil nil
  :pred certificate-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-prop ((prop proposalp) (certs certificate-setp))
  :returns (certs-with-prop certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given proposal."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       (cert (set::head certs)))
    (if (equal (certificate->proposal cert)
               (proposal-fix prop))
        (set::insert cert (certs-with-prop prop (set::tail certs)))
      (certs-with-prop prop (set::tail certs))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret certs-with-prop-subset
    (set::subset certs-with-prop certs)
    :hyp (certificate-setp certs)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defruled cert-set->prop-set-of-certs-with-prop
    (equal (cert-set->prop-set (certs-with-prop prop certs))
           (if (set::emptyp (certs-with-prop prop certs))
               nil
             (set::insert (proposal-fix prop) nil)))
    :induct t
    :enable cert-set->prop-set-of-insert)

  (defruled in-of-certs-with-prop
    (equal (set::in cert (certs-with-prop prop certs))
           (and (certificatep cert)
                (set::in cert (certificate-set-fix certs))
                (equal (certificate->proposal cert)
                       (proposal-fix prop))))
    :induct t)

  (defruled certs-with-prop-monotone
    (implies (set::subset (certificate-set-fix certs1)
                          (certificate-set-fix certs2))
             (set::subset (certs-with-prop prop certs1)
                          (certs-with-prop prop certs2)))
    :enable (in-of-certs-with-prop
             set::expensive-rules)
    :disable certs-with-prop)

  (defruled emptyp-of-certs-with-prop
    (equal (set::emptyp (certs-with-prop prop certs))
           (not (set::in (proposal-fix prop)
                         (cert-set->prop-set certs))))
    :induct t
    :enable cert-set->prop-set)

  (defrule certs-with-prop-of-nil
    (equal (certs-with-prop prop nil)
           nil))

  (defruled certificate->proposal-when-in-certs-with-prop
    (implies (set::in cert (certs-with-prop prop certs))
             (equal (certificate->proposal cert)
                    (proposal-fix prop)))
    :enable in-of-certs-with-prop
    :disable certs-with-prop)

  (defruled certificate->proposal-of-head-of-certs-with-prop
    (implies (not (set::emptyp (certs-with-prop prop certs)))
             (equal (certificate->proposal
                     (set::head (certs-with-prop prop certs)))
                    (proposal-fix prop)))
    :use (:instance certificate->proposal-when-in-certs-with-prop
                    (cert (set::head (certs-with-prop prop certs))))
    :disable certs-with-prop))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-author+round ((author addressp)
                                 (round posp)
                                 (certs certificate-setp))
  :returns (certs-with-author+round certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given author and round."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       (cert (set::head certs)))
    (if (and (equal (certificate->author cert)
                    (address-fix author))
             (equal (certificate->round cert)
                    (pos-fix round)))
        (set::insert (certificate-fix cert)
                     (certs-with-author+round author round (set::tail certs)))
      (certs-with-author+round author round (set::tail certs))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret certs-with-author+round-subset
    (set::subset certs-with-author+round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defruled cert-set->author-set-of-certs-with-author+round
    (equal (cert-set->author-set
            (certs-with-author+round author round certs))
           (if (set::emptyp
                (certs-with-author+round author round certs))
               nil
             (set::insert (address-fix author) nil)))
    :induct t
    :enable cert-set->author-set-of-insert)

  (defruled cert-set->round-set-of-certs-with-author+round
    (equal (cert-set->round-set
            (certs-with-author+round author round certs))
           (if (set::emptyp
                (certs-with-author+round author round certs))
               nil
             (set::insert (pos-fix round) nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled in-of-certs-with-author+round
    (equal (set::in cert (certs-with-author+round author round certs))
           (and (certificatep cert)
                (set::in cert (certificate-set-fix certs))
                (equal (certificate->author cert)
                       (address-fix author))
                (equal (certificate->round cert)
                       (pos-fix round))))
    :induct t)

  (defruled certs-with-author+round-monotone
    (implies (set::subset (certificate-set-fix certs1)
                          (certificate-set-fix certs2))
             (set::subset (certs-with-author+round author round certs1)
                          (certs-with-author+round author round certs2)))
    :enable (in-of-certs-with-author+round
             set::expensive-rules)
    :disable certs-with-author+round)

  (defrule certs-with-author+round-of-nil
    (equal (certs-with-author+round author round nil)
           nil))

  (defruled certs-with-author+round-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certs-with-author+round author
                                             round
                                             (set::insert cert certs))
                    (if (and (equal (certificate->author cert)
                                    (address-fix author))
                             (equal (certificate->round cert)
                                    (pos-fix round)))
                        (set::insert cert
                                     (certs-with-author+round author
                                                              round
                                                              certs))
                      (certs-with-author+round author round certs))))
    :enable (in-of-certs-with-author+round
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable certs-with-author+round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cert-with-author+round ((author addressp)
                                (round posp)
                                (certs certificate-setp))
  :returns (cert? certificate-optionp)
  :short "Retrieve, from a set of certificates,
          the certificate with a given author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there is no certificate with the given author and round,
     or if there is more than one,
     @('nil') is returned, for no certificate.
     Otherwise, if there is exactly one certificate with that author and round,
     the certificate is returned."))
  (b* ((certs-ar (certs-with-author+round author round certs))
       ((unless (= (set::cardinality certs-ar) 1)) nil))
    (certificate-fix (set::head certs-ar)))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))
  :hooks (:fix)

  ///

  (defrule certificate->author-of-cert-with-author+round
    (implies (cert-with-author+round author round certs)
             (equal (certificate->author
                     (cert-with-author+round author round certs))
                    (address-fix author)))
    :use (cert-set->author-set-of-certs-with-author+round
          (:instance certificate->author-in-cert-set->author-set
                     (cert (set::head
                            (certs-with-author+round author round certs)))
                     (certs (certs-with-author+round author round certs))))
    :enable set::cardinality)

  (defrule certificate->round-of-cert-with-author+round
    (implies (cert-with-author+round author round certs)
             (equal (certificate->round
                     (cert-with-author+round author round certs))
                    (pos-fix round)))
    :use (cert-set->round-set-of-certs-with-author+round
          (:instance certificate->round-in-cert-set->round-set
                     (cert (set::head
                            (certs-with-author+round author round certs)))
                     (certs (certs-with-author+round author round certs))))
    :enable set::cardinality))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-round ((round posp) (certs certificate-setp))
  :returns (certs-with-round certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given round."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       (cert (set::head certs)))
    (if (equal (certificate->round cert)
               (pos-fix round))
        (set::insert (certificate-fix cert)
                     (certs-with-round round (set::tail certs)))
      (certs-with-round round (set::tail certs))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret certs-with-round-subset
    (set::subset certs-with-round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defruled cert-set->round-set-of-certs-with-round
    (equal (cert-set->round-set (certs-with-round round certs))
           (if (set::emptyp (certs-with-round round certs))
               nil
             (set::insert (pos-fix round) nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled in-of-certs-with-round
    (equal (set::in cert (certs-with-round round certs))
           (and (certificatep cert)
                (set::in cert (certificate-set-fix certs))
                (equal (certificate->round cert)
                       (pos-fix round))))
    :induct t)

  (defruled certs-with-round-monotone
    (implies (set::subset (certificate-set-fix certs1)
                          (certificate-set-fix certs2))
             (set::subset (certs-with-round round certs1)
                          (certs-with-round round certs2)))
    :enable (in-of-certs-with-round
             set::expensive-rules)
    :disable certs-with-round)

  (defruled certs-with-round-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certs-with-round round
                                      (set::insert cert certs))
                    (if (equal (certificate->round cert)
                               (pos-fix round))
                        (set::insert cert
                                     (certs-with-round round certs))
                      (certs-with-round round certs))))
    :enable (in-of-certs-with-round
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable certs-with-round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-authors+round ((authors address-setp)
                                  (round posp)
                                  (certs certificate-setp))
  :returns (certs-with-authors+round certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates
          with author in a given set and with a given round."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       (cert (set::head certs)))
    (if (and (set::in (certificate->author cert)
                      (address-set-fix authors))
             (equal (certificate->round cert)
                    (pos-fix round)))
        (set::insert (certificate-fix cert)
                     (certs-with-authors+round authors
                                               round
                                               (set::tail certs)))
      (certs-with-authors+round authors
                                round
                                (set::tail certs))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret certs-with-authors+round-subset
    (set::subset certs-with-authors+round certs)
    :hyp (certificate-setp certs)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defruled cert-set->round-set-of-certs-with-authors+round
    (equal (cert-set->round-set
            (certs-with-authors+round authors round certs))
           (if (set::emptyp
                (certs-with-authors+round authors round certs))
               nil
             (set::insert (pos-fix round) nil)))
    :induct t
    :enable cert-set->round-set-of-insert)

  (defruled in-of-certs-with-authors+round
    (equal (set::in cert (certs-with-authors+round authors round certs))
           (and (certificatep cert)
                (set::in cert (certificate-set-fix certs))
                (set::in (certificate->author cert)
                         (address-set-fix authors))
                (equal (certificate->round cert)
                       (pos-fix round))))
    :induct t)

  (defruled certs-with-authors+round-monotone
    (implies (set::subset (certificate-set-fix certs1)
                          (certificate-set-fix certs2))
             (set::subset (certs-with-authors+round authors round certs1)
                          (certs-with-authors+round authors round certs2)))
    :enable (in-of-certs-with-authors+round
             set::expensive-rules)
    :disable certs-with-authors+round)

  (defruled certs-with-authors+round-of-insert
    (implies (and (certificatep cert)
                  (certificate-setp certs))
             (equal (certs-with-authors+round authors
                                              round
                                              (set::insert cert certs))
                    (if (and (set::in (certificate->author cert)
                                      (address-set-fix authors))
                             (equal (certificate->round cert)
                                    (pos-fix round)))
                        (set::insert cert
                                     (certs-with-authors+round authors
                                                               round
                                                               certs))
                      (certs-with-authors+round authors round certs))))
    :enable (in-of-certs-with-authors+round
             set::double-containment-no-backchain-limit
             set::pick-a-point-subset-strategy)
    :disable certs-with-authors+round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist cert-list-evenp (x)
  :guard (certificate-listp x)
  :short "Check if
          the round numbers of all the certificates in a list are even."
  (evenp (certificate->round x))
  ///
  (fty::deffixequiv cert-list-evenp
    :args ((x certificate-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cert-list-orderedp ((certs certificate-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of certificates has
          strictly increasing round numbers from right to left."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to @(tsee blocks-orderedp),
     but for certificates instead of blocks.
     The reason for having this predicate on certificates is that
     blockchains are extended from sequences of anchors,
     which are lists of certificates;
     the reason why blocks have strictly increasing round numbers
     is that the collected lists of anchors also have
     strictly increasing round numbers."))
  (b* (((when (endp certs)) t)
       ((when (endp (cdr certs))) t)
       ((unless (> (certificate->round (car certs))
                   (certificate->round (cadr certs))))
        nil))
    (cert-list-orderedp (cdr certs)))
  :hooks (:fix))
