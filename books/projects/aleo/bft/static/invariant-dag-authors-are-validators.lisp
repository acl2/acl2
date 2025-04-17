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

(include-book "invariant-signers-are-validators")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ invariant-dag-authors-are-validators
  :parents (correctness)
  :short "Invariant that all the authors of certificates in each DAG
          are validators in the system."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a specialization of @(see invariant-signers-are-validators),
     restricted to just authors of DAGs.
     It is expressed in terms of
     the set of authors of all the cerficates in each DAG;
     this form is used in further correctness proofs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define dag-authors-are-validators-p ((dag certificate-setp)
                                      (vals address-setp))
  :returns (yes/no booleanp)
  :short "Check if all the authors of certificates in a dag
          are a subset of a given set of validator addresses."
  (set::subset (cert-set->author-set dag) vals))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk system-authors-are-validators-p ((systate system-statep))
  :returns (yes/no booleanp)
  :short "Definition of the invariant:
          the set of authors of the DAG of each validator
          is a subset of
          the set of the addresses of the validators in the system."
  (forall (val)
          (implies (set::in val (correct-addresses systate))
                   (dag-authors-are-validators-p
                    (validator-state->dag
                     (get-validator-state val systate))
                    (all-addresses systate))))
  :guard-hints
  (("Goal" :in-theory (enable in-all-addresses-when-in-correct-addresses))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection system-authors-are-validators-p-when-signers-are-validators
  :short "Proof that the invariant is a consequence of
          the invariant that signers are validators."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is conceptually simple, but it takes a bit of work
     just because of the difference in the definition structure of
     @(tsee system-signers-are-validators-p) and
     @(tsee system-authors-are-validators-p).
     The former quantifies over validator addresses and certificates,
     while the latter only quantifies over validator addresses.
     To use the @('-necc') theorem of the former to prove the latter,
     we need to instantiate the certificate variable @('cert').
     We do so by picking an element of the DAG,
     via the local function @('thecert') defined below.
     This function is called on the DAG.
     Its author input is a generic one
     used in the local theorem @('subset-lemma'),
     used in the main theorem to prove the subset relation
     via the oset pick-a-point approach.")
   (xdoc::p
    "The @('thecert') function returns
     the first certificate with the given author
     (any other certificate in the set would do,
     but @(tsee set::head) is a simple way to pick an element from a set).
     The key property of the function @('thecert') are that,
     under the assumption that the author is in the set
     (in the sense that some certificate in the set has that author),
     the function returns a certificate in the set with that author.
     This is proved in the local @('thecert-lemma') below.
     This lemma fires as a rewrite rule in @('subset-lemma'),
     which in turns fires as a rewrite rule in the main theorem."))

  (local
   (defund thecert (author certs)
     (set::head (certs-with-author author certs))))

  (defrulel thecert-lemma
    (implies (and (certificate-setp certs)
                  (set::in author (cert-set->author-set certs)))
             (and (set::in (thecert author certs) certs)
                  (equal (certificate->author (thecert author certs))
                         author)))
    :use (:instance set::in-head (x (certs-with-author author certs)))
    :enable (thecert
             in-of-certs-with-author
             emptyp-of-certs-with-author))

  (defrulel subset-lemma
    (implies (and (system-signers-are-validators-p systate)
                  (set::in val (correct-addresses systate))
                  (set::in author
                           (cert-set->author-set
                            (validator-state->dag
                             (get-validator-state val systate)))))
             (set::in author (all-addresses systate)))
    :use ((:instance system-signers-are-validators-p-necc
                     (cert (thecert author
                                    (validator-state->dag
                                     (get-validator-state val systate))))))
    :enable (certificates-for-validator
             certificate-signers-are-validators-p
             certificate->signers))

  (defruled system-authors-are-validators-p-when-signers-are-validators
    (implies (system-signers-are-validators-p systate)
             (system-authors-are-validators-p systate))
    :enable (system-authors-are-validators-p
             dag-authors-are-validators-p
             set::expensive-rules)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled system-authors-are-validators-p-when-reachable
  :short "The invariant holds in every reachable state."
  :long
  (xdoc::topstring
   (xdoc::p
    "Reachable states are characterized by an initial state and
     a sequence of possible events from that initial state."))
  (implies (and (system-statep systate)
                (system-state-initp systate)
                (events-possiblep events systate))
           (system-authors-are-validators-p (events-next events systate)))
  :disable ((:e tau-system))
  :enable (system-authors-are-validators-p-when-signers-are-validators
           system-signers-are-validators-p-when-reachable))
