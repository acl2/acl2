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

(include-book "../library-extensions/oset-nonemptyp")

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
    :enable certificate->author-in-cert-set->author-set)

  (defruled same-certificate-author-when-cardinality-leq-1
    (implies (and (certificate-setp certs)
                  (<= (set::cardinality (cert-set->author-set certs)) 1)
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
    :enable certificate->round-in-cert-set->round-set)

  (defruled same-certificate-round-when-cardinality-leq-1
    (implies (and (certificate-setp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
             (equal (certificate->round cert1)
                    (certificate->round cert2)))
    :enable certificate->round-in-cert-set->round-set
    :use (:instance set::same-element-when-cardinality-leq-1
                    (elem1 (certificate->round cert1))
                    (elem2 (certificate->round cert2))
                    (set (cert-set->round-set certs)))))

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
                  (set::in cert certs)
                  (equal (certificate->proposal cert) prop))
             (set::in prop (cert-set->prop-set certs)))
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

  (defrule certs-with-prop-of-empty
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

(defsection cert-set->prop-set-ext
  :extension cert-set->prop-set

  (defruled in-of-cert-set->prop-set
    (implies (certificate-setp certs)
             (equal (set::in prop (cert-set->prop-set certs))
                    (b* ((cert (set::nonempty-witness
                                (certs-with-prop prop certs))))
                      (and (set::in cert certs)
                           (equal (certificate->proposal cert)
                                  prop)))))
    :use (only-if-part if-part)

    :prep-lemmas

    ((defruled only-if-part
       (implies (certificate-setp certs)
                (implies (set::in prop (cert-set->prop-set certs))
                         (b* ((cert (set::nonempty-witness
                                     (certs-with-prop prop certs))))
                           (and (set::in cert certs)
                                (equal (certificate->proposal cert)
                                       prop)))))
       :use (:instance set::nonemptyp-when-not-emptyp
                       (set (certs-with-prop prop certs)))
       :enable (set::nonemptyp
                in-of-certs-with-prop
                emptyp-of-certs-with-prop))

     (defruled if-part
       (implies (certificate-setp certs)
                (b* ((cert (set::nonempty-witness
                            (certs-with-prop prop certs))))
                  (implies (and (set::in cert certs)
                                (equal (certificate->proposal cert)
                                       prop))
                           (set::in prop (cert-set->prop-set certs)))))
       :use (:instance certificate->proposal-in-cert-set->prop-set
                       (cert (set::nonempty-witness
                              (certs-with-prop prop certs))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-author ((author addressp) (certs certificate-setp))
  :returns (certs-with-author certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given author."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       (cert (set::head certs)))
    (if (equal (certificate->author cert)
               (address-fix author))
        (set::insert cert (certs-with-author author (set::tail certs)))
      (certs-with-author author (set::tail certs))))
  :prepwork ((local (in-theory (enable emptyp-of-certificate-set-fix))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defret certs-with-author-subset
    (set::subset certs-with-author certs)
    :hyp (certificate-setp certs)
    :hints (("Goal" :induct t :in-theory (enable* set::expensive-rules))))

  (defruled cert-set->author-set-of-certs-with-author
    (equal (cert-set->author-set (certs-with-author author certs))
           (if (set::emptyp (certs-with-author author certs))
               nil
             (set::insert (address-fix author) nil)))
    :induct t
    :enable cert-set->author-set-of-insert)

  (defruled in-of-certs-with-author
    (equal (set::in cert (certs-with-author author certs))
           (and (certificatep cert)
                (set::in cert (certificate-set-fix certs))
                (equal (certificate->author cert)
                       (address-fix author))))
    :induct t)

  (defruled certs-with-author-monotone
    (implies (set::subset (certificate-set-fix certs1)
                          (certificate-set-fix certs2))
             (set::subset (certs-with-author author certs1)
                          (certs-with-author author certs2)))
    :enable (in-of-certs-with-author
             set::expensive-rules)
    :disable certs-with-author)

  (defruled emptyp-of-certs-with-author
    (equal (set::emptyp (certs-with-author author certs))
           (not (set::in (address-fix author)
                         (cert-set->author-set certs))))
    :induct t
    :enable cert-set->author-set)

  (defruled certs-with-author-of-insert
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

  (defruled cardinality-of-author-set-of-certs-with-author-leq-1
    (<= (set::cardinality
         (cert-set->author-set
          (certs-with-author author certs)))
        1)
    :rule-classes :linear
    :enable (cert-set->author-set-of-certs-with-author
             set::cardinality)
    :disable certs-with-author))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection cert-set->author-set-ext
  :extension cert-set->author-set

  (defruled in-of-cert-set->author-set
    (implies (certificate-setp certs)
             (equal (set::in author (cert-set->author-set certs))
                    (b* ((cert (set::nonempty-witness
                                (certs-with-author author certs))))
                      (and (set::in cert certs)
                           (equal (certificate->author cert)
                                  author)))))
    :use (only-if-part if-part)

    :prep-lemmas

    ((defruled only-if-part
       (implies (certificate-setp certs)
                (implies (set::in author (cert-set->author-set certs))
                         (b* ((cert (set::nonempty-witness
                                     (certs-with-author author certs))))
                           (and (set::in cert certs)
                                (equal (certificate->author cert)
                                       author)))))
       :use (:instance set::nonemptyp-when-not-emptyp
                       (set (certs-with-author author certs)))
       :enable (set::nonemptyp
                in-of-certs-with-author
                emptyp-of-certs-with-author))

     (defruled if-part
       (implies (certificate-setp certs)
                (b* ((cert (set::nonempty-witness
                            (certs-with-author author certs))))
                  (implies (and (set::in cert certs)
                                (equal (certificate->author cert)
                                       author))
                           (set::in author (cert-set->author-set certs)))))
       :use (:instance certificate->author-in-cert-set->author-set
                       (cert (set::nonempty-witness
                              (certs-with-author author certs))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certs-with-round ((round posp) (certs certificate-setp))
  :returns (certs-with-round certificate-setp)
  :short "Retrieve, from a set of certificates,
          the subset of certificates with a given round."
  (b* (((when (set::emptyp (certificate-set-fix certs))) nil)
       (cert (set::head certs)))
    (if (equal (certificate->round cert)
               (pos-fix round))
        (set::insert cert (certs-with-round round (set::tail certs)))
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

  (defruled emptyp-of-certs-with-round
    (equal (set::emptyp (certs-with-round round certs))
           (not (set::in (pos-fix round)
                         (cert-set->round-set certs))))
    :induct t
    :enable cert-set->round-set)

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
    :disable certs-with-round)

  (defruled cardinality-of-round-set-of-certs-with-round-leq-1
    (<= (set::cardinality
         (cert-set->round-set
          (certs-with-round round certs)))
        1)
    :rule-classes :linear
    :enable (cert-set->round-set-of-certs-with-round
             set::cardinality)
    :disable certs-with-round))

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
        (set::insert cert (certs-with-author+round author round (set::tail certs)))
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

  (defruled not-emptyp-of-certs-with-author+round
    (implies (and (set::in cert certs)
                  (certificate-setp certs)
                  (equal (certificate->author cert) author)
                  (equal (certificate->round cert) round))
             (not (set::emptyp (certs-with-author+round author round certs))))
    :induct t)

  (defruled certs-with-author+round-monotone
    (implies (set::subset (certificate-set-fix certs1)
                          (certificate-set-fix certs2))
             (set::subset (certs-with-author+round author round certs1)
                          (certs-with-author+round author round certs2)))
    :enable (in-of-certs-with-author+round
             set::expensive-rules)
    :disable certs-with-author+round)

  (defruled certificate->author-when-in-certs-with-author+round
    (implies (set::in cert (certs-with-author+round author round certs))
             (equal (certificate->author cert)
                    (address-fix author)))
    :rule-classes :forward-chaining
    :enable in-of-certs-with-author+round
    :disable certs-with-author+round)

  (defruled certificate->round-when-in-certs-with-author+round
    (implies (set::in cert (certs-with-author+round author round certs))
             (equal (certificate->round cert)
                    (pos-fix round)))
    :rule-classes :forward-chaining
    :enable in-of-certs-with-author+round
    :disable certs-with-author+round)

  (defrule certs-with-author+round-of-empty
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
    :disable certs-with-author+round)

  (defruled certs-with-author+round-to-author-of-round
    (implies (certificate-setp certs)
             (equal (certs-with-author+round author round certs)
                    (certs-with-author author (certs-with-round round certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certs-with-author+round
             in-of-certs-with-author
             in-of-certs-with-round)
    :disable certs-with-author+round)

  (defruled certs-with-author+round-to-round-of-author
    (implies (certificate-setp certs)
             (equal (certs-with-author+round author round certs)
                    (certs-with-round round (certs-with-author author certs))))
    :enable (set::expensive-rules
             set::double-containment-no-backchain-limit
             in-of-certs-with-author+round
             in-of-certs-with-author
             in-of-certs-with-round)
    :disable certs-with-author+round))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define cert-with-author+round ((author addressp)
                                (round posp)
                                (certs certificate-setp))
  :returns (cert? certificate-optionp
                  :hints (("Goal" :in-theory (enable certificate-optionp))))
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
    (set::head certs-ar))
  :guard-hints (("Goal" :in-theory (enable set::cardinality)))
  :hooks (:fix)

  ///

  (defret cert-with-author+round-element
    (implies cert?
             (set::in cert? certs))
    :hyp (certificate-setp certs)
    :hints (("Goal"
             :in-theory (e/d* (set::expensive-rules)
                              (set::in-head))
             :use (:instance set::in-head
                             (x (certs-with-author+round
                                 author round certs))))))
  (in-theory (disable cert-with-author+round-element))

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
    :enable set::cardinality)

  (defruled cert-with-author+round-of-insert
    (implies (and (certificate-setp certs)
                  (certificatep cert)
                  (cert-with-author+round author round certs))
             (equal (cert-with-author+round
                     author round (set::insert cert certs))
                    (if (set::in cert certs)
                        (cert-with-author+round author round certs)
                      (if (and (equal (certificate->author cert)
                                      (address-fix author))
                               (equal (certificate->round cert)
                                      (pos-fix round)))
                          nil
                        (cert-with-author+round author round certs)))))
    :use (lemma1 lemma2)
    :prep-lemmas
    ((defruled lemma1
       (implies (and (certificate-setp certs)
                     (certificatep cert)
                     (not (set::in cert certs))
                     (cert-with-author+round author round certs))
                (equal (cert-with-author+round
                        author round (set::insert cert certs))
                       (if (and (equal (certificate->author cert)
                                       (address-fix author))
                                (equal (certificate->round cert)
                                       (pos-fix round)))
                           nil
                         (cert-with-author+round author round certs))))
       :enable (cert-with-author+round
                certs-with-author+round-of-insert
                set::expensive-rules))
     (defruled lemma2
       (implies (set::in cert certs)
                (equal (cert-with-author+round
                        author round (set::insert cert certs))
                       (cert-with-author+round author round certs)))))))

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
        (set::insert cert
                     (certs-with-authors+round authors round (set::tail certs)))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certs-with-author+round-and-props-with-author+round
  :short "Theorems relating
          @(tsee certs-with-author+round),
          @(tsee props-with-author+round), and
          @(tsee cert-set->prop-set)."

  (defruled cert-set->prop-set-of-certs-with-author+round
    (implies (certificate-setp certs)
             (equal (cert-set->prop-set
                     (certs-with-author+round author round certs))
                    (props-with-author+round
                     author round (cert-set->prop-set certs))))
    :enable (set::double-containment-no-backchain-limit
             set::expensive-rules)

    :prep-lemmas

    ((defrule one
       (implies (certificate-setp certs)
                (implies (set::in prop
                                  (cert-set->prop-set
                                   (certs-with-author+round
                                    author round certs)))
                         (set::in prop
                                  (props-with-author+round
                                   author round (cert-set->prop-set certs)))))
       :use (:instance certificate->proposal-in-cert-set->prop-set
                       (cert (SET::NONEMPTY-WITNESS
                              (certs-with-prop
                               prop (certs-with-author+round
                                     author round certs)))))
       :enable (in-of-cert-set->prop-set
                in-of-certs-with-author+round
                in-of-props-with-author+round
                certificate->author
                certificate->round))

     (defrule two
       (implies (certificate-setp certs)
                (implies (set::in prop
                                  (props-with-author+round
                                   author round (cert-set->prop-set certs)))
                         (set::in prop
                                  (cert-set->prop-set
                                   (certs-with-author+round
                                    author round certs)))))
       :use (:instance certificate->proposal-in-cert-set->prop-set
                       (cert (set::nonempty-witness
                              (certs-with-prop prop certs)))
                       (certs (certs-with-author+round author round certs)))
       :enable (in-of-props-with-author+round
                in-of-cert-set->prop-set
                in-of-certs-with-author+round
                certificate->author
                certificate->round))))

  (defruled props-with-author+round-of-cert-set->prop-set
    (implies (certificate-setp certs)
             (equal (props-with-author+round
                     author round (cert-set->prop-set certs))
                    (cert-set->prop-set
                     (certs-with-author+round author round certs))))
    :enable cert-set->prop-set-of-certs-with-author+round)

  (theory-invariant
   (incompatible (:rewrite cert-set->prop-set-of-certs-with-author+round)
                 (:rewrite props-with-author+round-of-cert-set->prop-set)))

  (defruled emptyp-of-certs-with-author+round-to-props
    (implies (certificate-setp certs)
             (equal (set::emptyp
                     (certs-with-author+round author round certs))
                    (set::emptyp
                     (props-with-author+round author
                                              round
                                              (cert-set->prop-set certs)))))
    :enable props-with-author+round-of-cert-set->prop-set)

  (defruled emptyp-of-props-with-author+round-of-cert-set->prop-set
    (implies (certificate-setp certs)
             (equal (set::emptyp
                     (certs-with-author+round author round certs))
                    (set::emptyp
                     (props-with-author+round author
                                              round
                                              (cert-set->prop-set certs)))))
    :enable emptyp-of-certs-with-author+round-to-props)

  (theory-invariant
   (incompatible
    (:rewrite emptyp-of-certs-with-author+round-to-props)
    (:rewrite emptyp-of-props-with-author+round-of-cert-set->prop-set))))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk cert-set-unequivp ((certs certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if a set of certificates is unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether the certificates in the set
     have unique combinations of author and round.
     We check that any two certificates in the set
     with the same author and round
     are in the same certificates.
     This means that the certificates in the set
     are uniquely identified by their author and round."))
  (forall (cert1 cert2)
          (implies (and (set::in cert1 (certificate-set-fix certs))
                        (set::in cert2 (certificate-set-fix certs))
                        (equal (certificate->author cert1)
                               (certificate->author cert2))
                        (equal (certificate->round cert1)
                               (certificate->round cert2)))
                   (equal cert1 cert2)))

  ///

  (fty::deffixequiv-sk cert-set-unequivp
    :args ((certs certificate-setp)))

  (defruled cert-set-unequivp-when-subset
    (implies (and (cert-set-unequivp certs)
                  (set::subset (certificate-set-fix certs0)
                               (certificate-set-fix certs)))
             (cert-set-unequivp certs0))
    :disable cert-set-unequivp-necc
    :use (:instance cert-set-unequivp-necc
                    (cert1 (mv-nth 0 (cert-set-unequivp-witness certs0)))
                    (cert2 (mv-nth 1 (cert-set-unequivp-witness certs0))))
    :enable set::expensive-rules)

  (defrule cert-set-unequivp-of-empty
    (cert-set-unequivp nil))

  (defruled cert-set-unequivp-of-insert
    (implies (and (certificate-setp certs)
                  (certificatep cert))
             (equal (cert-set-unequivp (set::insert cert certs))
                    (and (cert-set-unequivp certs)
                         (or (set::in cert certs)
                             (set::emptyp (certs-with-author+round
                                           (certificate->author cert)
                                           (certificate->round cert)
                                           certs))))))
    :use (if-part only-if-part)
    :prep-lemmas
    ((defruled if-part
       (implies (and (certificate-setp certs)
                     (certificatep cert)
                     (cert-set-unequivp certs)
                     (or (set::in cert certs)
                         (set::emptyp (certs-with-author+round
                                       (certificate->author cert)
                                       (certificate->round cert)
                                       certs))))
                (cert-set-unequivp (set::insert cert certs)))
       :use (:instance cert-set-unequivp-necc
                       (cert1 (mv-nth 0 (cert-set-unequivp-witness
                                         (set::insert cert certs))))
                       (cert2 (mv-nth 1 (cert-set-unequivp-witness
                                         (set::insert cert certs))))
                       (certs certs))
       :enable not-emptyp-of-certs-with-author+round
       :disable cert-set-unequivp-necc)
     (defruled only-if-part
       (implies (and (certificate-setp certs)
                     (certificatep cert)
                     (cert-set-unequivp (set::insert cert certs)))
                (and (cert-set-unequivp certs)
                     (or (set::in cert certs)
                         (set::emptyp (certs-with-author+round
                                       (certificate->author cert)
                                       (certificate->round cert)
                                       certs)))))
       :enable (cert-set-unequivp-when-subset
                set::emptyp-to-not-nonemptyp
                set::nonemptyp
                in-of-certs-with-author+round)
       :disable (cert-set-unequivp
                 cert-set-unequivp-necc)
       :use (:instance cert-set-unequivp-necc
                       (cert1 cert)
                       (cert2 (set::nonempty-witness
                               (certs-with-author+round
                                (certificate->author cert)
                                (certificate->round cert)
                                certs)))
                       (certs (set::insert cert certs))))))

  (defruled equal-cert-authors-when-unequivp-and-same-round
    (implies (and (certificate-setp certs)
                  (cert-set-unequivp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
             (equal (equal (certificate->author cert1)
                           (certificate->author cert2))
                    (equal cert1 cert2)))
    :use (cert-set-unequivp-necc
          same-certificate-round-when-cardinality-leq-1)
    :disable (cert-set-unequivp
              cert-set-unequivp-necc))

  (defruled equal-cert-rounds-when-unequivp-and-same-author
    (implies (and (certificate-setp certs)
                  (cert-set-unequivp certs)
                  (<= (set::cardinality (cert-set->author-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs))
             (equal (equal (certificate->round cert1)
                           (certificate->round cert2))
                    (equal cert1 cert2)))
    :use (cert-set-unequivp-necc
          same-certificate-author-when-cardinality-leq-1)
    :disable (cert-set-unequivp
              cert-set-unequivp-necc)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk cert-sets-unequivp ((certs1 certificate-setp)
                               (certs2 certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if two sets of certificates are unequivocal."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether any two certificates from the two sets
     (one from the first set, one from the second set)
     have the same proposal if they have the same author and round.
     This is a little weaker than requiring that
     the two certificates are equal:
     we allow the endorsers to differ.
     The reason is that AleoBFT cannot prevent a faulty validator
     from collecting more than a quorum of endorsements for a proposals
     and then sending slightly different certificates to different validators,
     where the certificates only differ in the endorsers.
     AleoBFT achieves nonequivocation of proposals in certificates,
     not of whole certificates."))
  (forall (cert1 cert2)
          (implies (and (set::in cert1 (certificate-set-fix certs2))
                        (set::in cert2 (certificate-set-fix certs2))
                        (equal (certificate->author cert1)
                               (certificate->author cert2))
                        (equal (certificate->round cert1)
                               (certificate->round cert2)))
                   (equal (certificate->proposal cert1)
                          (certificate->proposal cert2))))

  ///

  (fty::deffixequiv-sk cert-sets-unequivp
    :args ((certs1 certificate-setp) (certs2 certificate-setp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection certs-with-author+round-of-unequiv
  :short "Theorems about @(tsee certs-with-author+round)
          on unequivocal sets of certificates."

  (defruled certs-with-author+round-superset-when-unequiv
    (implies (and (certificate-setp certs)
                  (cert-set-unequivp certs)
                  (certificate-setp certs0)
                  (set::subset certs0 certs)
                  (not (set::emptyp
                        (certs-with-author+round author round certs0))))
             (equal (certs-with-author+round author round certs)
                    (certs-with-author+round author round certs0)))
    :enable (set::double-containment-no-backchain-limit
             certs-with-author+round-monotone)
    :prep-lemmas
    ((defrule lemma
       (implies (and (certificate-setp certs)
                     (cert-set-unequivp certs)
                     (certificate-setp certs0)
                     (set::subset certs0 certs)
                     (not (set::emptyp
                           (certs-with-author+round author round certs0))))
                (set::subset (certs-with-author+round author round certs)
                             (certs-with-author+round author round certs0)))
       :use ((:instance set::nonempty-witness-from-not-emptyp
                        (set (certs-with-author+round author round certs0)))
             (:instance cert-set-unequivp-necc
                        (cert1 (set::nonempty-witness
                                (certs-with-author+round author round certs0)))
                        (cert2 (set::subset-witness
                                (certs-with-author+round author round certs)
                                (certs-with-author+round author round certs0)))
                        (certs certs)))
       :enable (set::subset-pick-a-point
                set::expensive-rules
                in-of-certs-with-author+round)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection cert-with-author+round-of-unequiv
  :short "Theorems about @(tsee cert-with-author+round)
          on unequivocal sets of certificates."

  (defruled cert-with-author+round-superset-when-unequiv
    (implies (and (certificate-setp certs)
                  (cert-set-unequivp certs)
                  (certificate-setp certs0)
                  (set::subset certs0 certs)
                  (cert-with-author+round author round certs0))
             (equal (cert-with-author+round author round certs)
                    (cert-with-author+round author round certs0)))
    :enable (cert-with-author+round
             certs-with-author+round-superset-when-unequiv)
    :cases ((set::emptyp (certs-with-author+round author round certs0)))))
