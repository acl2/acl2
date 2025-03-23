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
      that this certificate is based on.")
    (xdoc::li
     "The addresses of the validators that endorsed this certificate,
      by signing it in addition to the author.
      We do not model the signing process here,
      but having a record of the signers (author and endorsers) serves
      to define the behavior and invariants of the model."))
   (xdoc::p
    "A validator generates at most one certificate per round.
     Thus, the combination of author and round number identifies
     (at most) a unique certificate in a DAG.")
   (xdoc::p
    "A certificate is a vertex of the DAG.
     The @('previous') component of this fixtype models
     the edges of the DAG, from this certificate to
     the certificates in the previous round
     with the authors specified by the set of addresses.")
   (xdoc::p
    "Since we model the exchange of proposals and signatures
     at a high level here,
     we do not distinguish between batch headers and batch certificates,
     and instead model certificates directly,
     as containing the information that is relevant to our model.
     The signatures are implicit:
     a certificate as modeled here is implicitly validated and signed
     by a quorum of validators (author and endorsers)."))
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
    :enable nil-not-in-certificate-set))

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
    (implies (certificate-setp certs2)
             (equal (certificate-set->author-set (set::union certs1 certs2))
                    (set::union (certificate-set->author-set certs1)
                                (certificate-set->author-set certs2))))
    :induct t
    :enable (certificate-set->author-set-of-insert
             set::union))

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
    (implies (certificate-setp certs2)
             (equal (certificate-set->round-set (set::union certs1 certs2))
                    (set::union (certificate-set->round-set certs1)
                                (certificate-set->round-set certs2))))
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
    "These are the author and the endorsers."))
  (b* (((certificate cert) cert))
    (set::insert cert.author cert.endorsers)))
