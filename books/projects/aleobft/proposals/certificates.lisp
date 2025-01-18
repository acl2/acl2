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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist certificate-list
  :short "Fixtype of lists of certificates."
  :elt-type certificate
  :true-listp t
  :elementp-of-nil nil
  :pred certificate-listp
  :prepwork ((local (in-theory (enable nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate->author ((cert certificatep))
  :returns (author addressp)
  :short "Author of (the proposal in) a certificate."
  (proposal->author (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate->round ((cert certificatep))
  :returns (round posp)
  :short "Round number of (the proposal in) a certificate."
  (proposal->round (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate->transactions ((cert certificatep))
  :returns (transactions transaction-listp)
  :short "List of transactions of (the proposal in) a certificate."
  (proposal->transactions (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define certificate->previous ((cert certificatep))
  :returns (previous address-setp)
  :short "Set of references to previous certificates
          of (the proposal in) a certificate."
  (proposal->previous (certificate->proposal cert))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
