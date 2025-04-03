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

(include-book "operations-unequivocal-certificates")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ properties-certificate-retrieval
  :parents (correctness)
  :short "Some properties of the certificate retrieval operations,
          when applied to unequivocal sets of certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "Some of these come in two forms:
     one involving retrieval from two sets of certificates in subset relation
     where the superset (and consequently the subset) is unequivocal;
     and one involving retrieval from two sets of certificates
     that are mutually unequivocal.")
   (xdoc::p
    "The significance of the first kind is that,
     as the DAG of a validator grows,
     the retrieval of existing certificates is unaffected,
     i.e. always yields the same results as the DAG grows.
     The significance of the second kind is that,
     across DAGs of different validators,
     the retrieval of common certificates yields the same results.
     In other words, there is a ``stability'', or ``consistency'',
     in certificate retrieval,
     both within a validator and across validators.")
   (xdoc::p
    "These properties are the basis for proving
     some higher-level properties of paths and histories in DAGS,
     namely that those are also stable and consistent
     within a validator as its DAG grows
     as well as across different validators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cert-with-author+round-of-element-when-unequivocal
  :short "If a certificate is in an unequivocal set,
          retrieving a certificate with the certificate's author and round
          will return the certificate itself."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is not the case unless the set is unequivocal:
     there could be multiple certificates with the same author and round,
     and the operation may not return the specific @('cert')."))
  (implies (and (certificate-setp certs)
                (certificate-set-unequivocalp certs)
                (set::in cert certs))
           (equal (cert-with-author+round (certificate->author cert)
                                                 (certificate->round cert)
                                                 certs)
                  cert))
  :enable (cert-with-author+round-element
           cert-with-author+round-when-element)
  :use (:instance certificate-set-unequivocalp-necc
                  (cert1 cert)
                  (cert2 (cert-with-author+round
                          (certificate->author cert)
                          (certificate->round cert)
                          certs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-set-unequivocalp-of-certs-with-authors
  :short "The certificates with given authors of an unequivocal DAG
          is also an unequivocal set of certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple consequence of the fact that
     a subset of an unequivocal set is also unequivocal,
     but it is convenient to have this as a rewrite rule."))
  (implies (and (certificate-setp certs)
                (certificate-set-unequivocalp certs))
           (certificate-set-unequivocalp
            (certs-with-authors authors certs)))
  :enable (certificate-set-unequivocalp-when-subset
           certs-with-authors-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-set-unequivocalp-of-certificates-with-round
  :short "The certificates with a given round of an unequivocal DAG
          is also an unequivocal set of certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a simple consequence of the fact that
     a subset of an unequivocal set is also unequivocal,
     but it is convenient to have this as a rewrite rule."))
  (implies (and (certificate-setp certs)
                (certificate-set-unequivocalp certs))
           (certificate-set-unequivocalp
            (certificates-with-round round certs)))
  :enable (certificate-set-unequivocalp-when-subset
           certificates-with-round-subset))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cert-with-author+round-of-unequivocal-superset
  :short "If a certificate with a certain author and round
          is retrieved from a subset of an unequivocal set of certificates,
          the same certificate is retrieved from the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "The significance is that, as the DAG of a validator grows,
     a certain author and round always denotes the same certificate.")
   (xdoc::p
    "See @(tsee cert-with-author+round-of-unequivocal-sets)
     for an analogous theorem involving two mutually unequivocal sets."))
  (implies (and (certificate-setp certs1)
                (certificate-setp certs2)
                (set::subset certs1 certs2)
                (certificate-set-unequivocalp certs2)
                (cert-with-author+round author round certs1))
           (equal (cert-with-author+round author round certs2)
                  (cert-with-author+round author round certs1)))
  :use (:instance certificate-set-unequivocalp-necc
                  (certs certs2)
                  (cert1
                   (cert-with-author+round author round certs1))
                  (cert2
                   (cert-with-author+round author round certs2)))
  :enable (cert-with-author+round-when-subset
           cert-with-author+round-element
           set::expensive-rules))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cert-with-author+round-of-unequivocal-sets
  :short "If a certificate with a certain author and round
          is retrieved from both of two mutually unequivocal certificate sets,
          it is the same certificate from both sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to
     @(tsee cert-with-author+round-of-unequivocal-superset),
     but for two mutually unequivocal certificate sets.")
   (xdoc::p
    "The significance is that a certain author and round
     denotes the same certificate in two validator DAGS,
     provided that both DAGs have a certificate for that author and round."))
  (implies (and (certificate-setp certs1)
                (certificate-setp certs2)
                (certificate-sets-unequivocalp certs1 certs2)
                (cert-with-author+round author round certs1)
                (cert-with-author+round author round certs2))
           (equal (cert-with-author+round author round certs1)
                  (cert-with-author+round author round certs2)))
  :enable (cert-with-author+round-element)
  :use (:instance
        certificate-sets-unequivocalp-necc
        (cert1 (cert-with-author+round author round certs1))
        (cert2 (cert-with-author+round author round certs2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certs-with-authors+round-of-unequivocal-superset
  :short "If certificates with certain authors and a certain round
          are retrieved from a subset of an unequivocal set of certificates,
          the same certificates are retrieved from the superset."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the hypothesis that the given authors are
     all in the certificates at the given round in the subset.
     That is, a certificates for each author is in the subset at the round.
     Otherwise, the superset could have additional certificates at the round,
     with authors not found in the subset at the round.")
   (xdoc::p
    "Although this theorem is formulated for a generic set of authors,
     its motivation is for the predecessor certificates of a certificate.
     Each certificate not at round 1 includes references to
     certificates in the previous round,
     in the form of the set of authors,
     which, together with the round number,
     uniquely identify certificates, in unequivocal DAGs.
     So in this theorem @('authors') stands for
     that set of authors of previous certificates from a certificate,
     and @('round') stands for the round number just before the cerfificate.
     (But it is a more general theorem, and it is formulated as such here.)
     So, when applied to such @('authors') and @('round'),
     this theorem tells us that the predecessor certificates
     do not change as the DAG grows,
     for existing certificates in the DAG.
     Obviously, newly added certificates to the DAG
     come with their own predecessors,
     but this theorem does not talk about newly added certificates:
     the hypothesis is that those predecessor certificates are in the subset.")
   (xdoc::p
    "See @(tsee certs-with-authors+round-of-unequivocal-sets)
     for an analogous theorem involving two mutually unequivocal sets."))
  (implies (and (certificate-setp certs1)
                (certificate-setp certs2)
                (set::subset certs1 certs2)
                (certificate-set-unequivocalp certs2)
                (set::subset authors
                             (cert-set->author-set
                              (certificates-with-round round certs1))))
           (equal (certs-with-authors+round authors round certs2)
                  (certs-with-authors+round authors round certs1)))
  :enable (set::expensive-rules
           set::double-containment-no-backchain-limit
           cert-with-author+round-when-author-in-round
           in-of-certs-with-authors+round)

  :prep-lemmas
  ((defrule lemma
     (implies (and (certificate-setp certs1)
                   (certificate-setp certs2)
                   (set::subset certs1 certs2)
                   (certificate-set-unequivocalp certs2)
                   (set::in cert certs2)
                   (cert-with-author+round (certificate->author cert)
                                                      (certificate->round cert)
                                                      certs1))
              (set::in cert certs1))
     :use (:instance certificate-set-unequivocalp-necc
                     (certs certs2)
                     (cert1 cert)
                     (cert2 (cert-with-author+round
                             (certificate->author cert)
                             (certificate->round cert)
                             certs1)))
     :enable (set::expensive-rules
              cert-with-author+round-element
              cert-with-author+round-of-unequivocal-superset))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certs-with-authors+round-of-unequivocal-sets
  :short "If certificates with certain authors and a certain round
          are retrieved from both of two mutually unequivocal certificate sets,
          the same certificates are retrieved from both sets."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is analogous to
     @(tsee certs-with-authors+round-of-unequivocal-superset),
     but for two mutually unequivocal certificate sets.
     As for that theorem, the purpose of this theorem is for
     the predecessor certificates of a given certificate.")
   (xdoc::p
    "Note the hypotheses that the authors are found in both sets,
     at the given round.
     Then the certificates must be the same in the two sets."))
  (implies (and (certificate-setp certs1)
                (certificate-setp certs2)
                (certificate-sets-unequivocalp certs1 certs2)
                (set::subset authors
                             (cert-set->author-set
                              (certificates-with-round round certs1)))
                (set::subset authors
                             (cert-set->author-set
                              (certificates-with-round round certs2))))
           (equal (certs-with-authors+round authors round certs1)
                  (certs-with-authors+round authors round certs2)))
  :enable (set::expensive-rules
           set::double-containment-no-backchain-limit
           in-of-certs-with-authors+round)

  :prep-lemmas

  ;; We introduce two lemmas, for the two parts of the set containment.
  ;; A plain :USE hint interferes with the pick-a-point stategy,
  ;; because instantiating CERT with SET::ARBITRARY-ELEMENT
  ;; causes the SET::ARBITRARY-ELEMENT introduced by pick-a-point to be renamed.
  ;; The first hypothesis in each lemma below is unnecessary to prove it,
  ;; but it serves to bind the free variables,
  ;; so they can fire in the proof of the theorem.

  ((defrule lemma1
     (implies (and
               (set::subset authors ; bind authors
                            (cert-set->author-set
                             (certificates-with-round
                              (certificate->round cert) certs1))) ; bind certs1
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
     :use ((:instance cert-with-author+round-element
                      (certs certs2)
                      (author (certificate->author cert))
                      (round (certificate->round cert)))
           (:instance certificate-sets-unequivocalp-necc
                      (cert1 cert)
                      (cert2 (cert-with-author+round
                              (certificate->author cert)
                              (certificate->round cert)
                              certs2))))
     :enable (set::expensive-rules
              cert-with-author+round-when-author-in-round))

   (defrule lemma2
     (implies (and
               (set::subset authors ; bind authors
                            (cert-set->author-set
                             (certificates-with-round
                              (certificate->round cert) certs2))) ; bind certs2
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
     :use ((:instance cert-with-author+round-element
                      (certs certs1)
                      (author (certificate->author cert))
                      (round (certificate->round cert)))
           (:instance certificate-sets-unequivocalp-necc
                      (cert1 (cert-with-author+round
                              (certificate->author cert)
                              (certificate->round cert)
                              certs1))
                      (cert2 cert)))
     :enable (set::expensive-rules
              cert-with-author+round-when-author-in-round))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled cardinality-of-certs-with-authors+round-when-subset
  :short "The number of certificates in a round with given authors,
          in an unequivocal DAG,
          is equal to the number of authors,
          if there is a certificate for each author in that round."
  (implies (and (certificate-setp certs)
                (certificate-set-unequivocalp certs)
                (address-setp authors)
                (set::subset authors
                             (cert-set->author-set
                              (certificates-with-round round certs))))
           (equal (set::cardinality
                   (certs-with-authors+round authors round certs))
                  (set::cardinality authors)))
  :use ((:instance cardinality-of-authors-when-same-round-and-unequiv
                   (certs
                    (certs-with-authors+round authors round certs)))
        (:instance cardinality-of-subset-of-round-set-of-round
                   (certs0 (certs-with-authors
                            authors
                            (certificates-with-round round certs)))))
  :disable (cardinality-of-authors-when-same-round-and-unequiv)
  :enable (certs-with-authors+round-to-authors-of-round
           author-set-of-certs-with-authors
           certs-with-authors-subset))
