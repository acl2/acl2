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

(include-book "system-states")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-previous-certificates
  :parents (operations)
  :short "Operations for handling previous certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "As defined in @(tsee certificate),
     every certificate (except in round 1)
     references certificates in the previous round.
     These references form the edges of the DAG.")
   (xdoc::p
    "We introduce operations to check whether
     validators have the previuos certificates
     referenced by a certificate.
     These are used both by authors and endorsers."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signer-has-previous-certificates-p ((signer addressp)
                                            (previous address-setp)
                                            (round posp)
                                            (systate system-statep))
  :guard (set::in signer (all-addresses systate))
  :returns (yes/no booleanp)
  :short "Check whether a validator who signed a certificate
          has the certificate's previous certificates in its DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used to define @(tsee signers-have-previous-certificates-p):
     see that function's documentation for motivation.
     This function performs the check on a single validator.
     If the validator is faulty, the check passes:
     there is no requirement on faulty validators from this standpoint.
     If the validator is correct,
     we check that either the round is 1
     (in which case there is no previous round and no previous certificates),
     or the authors of the certificates in the previous round
     include all the ones referenced in the certificate."))
  (b* ((vstate (get-validator-state signer systate))
       ((when (not vstate)) t)
       ((when (= round 1)) t)
       (dag (validator-state->dag vstate))
       (previous-round (1- round))
       (previous-certs (certificates-with-round previous-round dag))
       (previous-authors (cert-set->author-set previous-certs)))
    (set::subset previous previous-authors))
  :guard-hints (("Goal" :in-theory (enable posp)))

  ///

  (fty::deffixequiv signer-has-previous-certificates-p
    :args ((systate system-statep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define signers-have-previous-certificates-p ((signers address-setp)
                                              (previous address-setp)
                                              (round posp)
                                              (systate system-statep))
  :guard (set::subset signers (all-addresses systate))
  :returns (yes/no booleanp)
  :short "Check whether all the correct validators who signed a certificate
          have the certificate's previous certificates in their DAG."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used by @(tsee create-certificate-possiblep)
     to express one of the conditions under which the event is possible.
     The condition is that
     every validator that signed a certificate,
     if it is a correct validator,
     has, in its DAG, all the previous certificates
     referenced in the signed certificates.")
   (xdoc::p
    "The first input to this ACL2 function consists of
     the signers (author and endorsers) of the certificate;
     see call in @(tsee create-certificate-possiblep)).
     The second input to this ACL2 function is
     the @('previous') component of the cerfificate.
     The third input to this ACL2 function is
     the @('round') component of the cerfificate.")
   (xdoc::p
    "If the certificate's round number is 1,
     then the check succeeds,
     because in that case there are no previous certificates.
     It is an invariant that if a certificate has round number 1
     then it has an empty set of previous (authors of) certificates;
     so @('previous') is @('nil') when @('round') is 1.")
   (xdoc::p
    "We go through each signer,
     and call the function to check an individual signer.
     The rationale is that, in AleoBFT,
     a correct validator will not sign a certificate
     unless it has all the referenced previous certificates.")
   (xdoc::p
    "Other requirements on the signed certificate's previous certificates
     that are not stated here (e.g. a lower bound on their number),
     are expressed in @(tsee create-certificate-possiblep)."))
  (or (set::emptyp signers)
      (and (signer-has-previous-certificates-p (set::head signers)
                                               previous round systate)
           (signers-have-previous-certificates-p (set::tail signers)
                                                 previous round systate)))
  :guard-hints (("Goal" :in-theory (enable* set::expensive-rules)))

  ///

  (fty::deffixequiv signers-have-previous-certificates-p
    :args ((systate system-statep)))

  (defruled signers-have-previous-certificates-p-element
    (implies (and (signers-have-previous-certificates-p signers
                                                        previous
                                                        round
                                                        systate)
                  (set::in signer signers))
             (signer-has-previous-certificates-p signer
                                                 previous
                                                 round
                                                 systate))
    :induct t))
