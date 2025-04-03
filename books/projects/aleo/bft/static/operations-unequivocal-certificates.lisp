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

(include-book "certificates")

(include-book "std/util/define-sk" :dir :system)

(local (include-book "../library-extensions/oset-theorems"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ operations-unequivocal-certificates
  :parents (operations-additional)
  :short "Operations about unequivocal certificates."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce predicates about unequivocal certificates
     within a single set of certificates
     as well as across two sets of certificates."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk certificate-set-unequivocalp ((certs certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if the certificates in a set have
          unique combinations of author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check whether
     any two certificates in the set with the same author and round
     are the same certificate.
     This means that the certificates in the set
     are uniquely identified by their author and round."))
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
    :expand (certificate-set-unequivocalp certs0)
    :use (:instance certificate-set-unequivocalp-necc
                    (cert1
                     (mv-nth 0 (certificate-set-unequivocalp-witness certs0)))
                    (cert2
                     (mv-nth 1 (certificate-set-unequivocalp-witness certs0))))
    :enable (set::expensive-rules
             in-of-certs-with-author)
    :disable certificate-set-unequivocalp)

  (defruled certificate-set-unequivocalp-of-tail
    (implies (certificate-set-unequivocalp certs)
             (certificate-set-unequivocalp (set::tail certs)))
    :enable certificate-set-unequivocalp-when-subset
    :disable certificate-set-unequivocalp)

  ;; If the certificates in a set are all in the same round,
  ;; which is expressed by saying that
  ;; the cardinality of the set of their rounds is 1 or less,
  ;; then if two certificates in the set have the same author,
  ;; they must be the same certificate, because the rounds are also the same.

  (defrule same-certificate-when-unequivocal-same-authors-and-round-card-leq-1
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1)
                  (set::in cert1 certs)
                  (set::in cert2 certs)
                  (equal (certificate->author cert1)
                         (certificate->author cert2)))
             (equal cert1 cert2))
    :rule-classes nil
    :use (certificate-set-unequivocalp-necc
          same-certificate-round-when-cardinality-leq-1))

  ;; The following is a consequence of the theorem above.
  ;; It says that in a non-empty set of
  ;; unequivocal certificates in the same round,
  ;; the author of the first (i.e. head) certificate
  ;; differs from the authors of the rest of the certificates.
  ;; It is a bit specific, but it is used to prove the next theorem below.

  (defruled head-author-not-in-tail-authors-when-same-round-and-unequiv
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (not (set::emptyp certs))
                  (<= (set::cardinality (cert-set->round-set certs)) 1))
             (not (set::in (certificate->author (set::head certs))
                           (cert-set->author-set (set::tail certs)))))
    :use ((:instance emptyp-of-certs-with-author-if-no-author
                     (author (certificate->author (set::head certs)))
                     (certs (set::tail certs)))
          (:instance
           same-certificate-when-unequivocal-same-authors-and-round-card-leq-1
           (cert1 (set::head certs))
           (cert2 (set::head (certs-with-author
                              (certificate->author (set::head certs))
                              (set::tail certs)))))
          (:instance set::in-head
                     (x (certs-with-author
                         (certificate->author (head certs))
                         (tail certs)))))
    :enable (set::expensive-rules
             in-of-certs-with-author))

  ;; In an unequivocal set of certificates in the same round,
  ;; the number of certificates is the same as the number of their authors.
  ;; This is because two different certificates cannot have the same author.

  (defruled cardinality-of-authors-when-same-round-and-unequiv
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (<= (set::cardinality (cert-set->round-set certs)) 1))
             (equal (set::cardinality (cert-set->author-set certs))
                    (set::cardinality certs)))
    :induct t
    :enable (set::cardinality
             cert-set->author-set
             head-author-not-in-tail-authors-when-same-round-and-unequiv
             set::expensive-rules)
    :disable (cert-set->round-set-monotone
              set::cardinality-of-tail-leq
              certificate-set-unequivocalp)
    :hints ('(:use ((:instance cert-set->round-set-monotone
                               (certs1 (set::tail certs))
                               (certs2 certs))
                    (:instance set::cardinality-of-tail-leq
                               (set (cert-set->round-set certs)))))))

  ;; The number of certificates in a round
  ;; is limited by the total number of validators in the system,
  ;; if the DAG is unequivocal.
  ;; The reason is that the certificates in a round
  ;; have a unique combination of author and round,
  ;; but since they all have the same round,
  ;; there must be at most one per author.
  ;; Here VALS stands for (the addresses of) all the validators in the system.
  ;; The theorem assumes that the authors of the certificates are among VALS.
  ;; It follows easily from the previous theorem that
  ;; the certificates must be at most as many as VALS.

  (defruled cardinality-bound-when-same-round-and-unequiv
    (implies (and (certificate-setp certs)
                  (certificate-set-unequivocalp certs)
                  (set::subset (cert-set->author-set certs) vals)
                  (<= (set::cardinality (cert-set->round-set certs)) 1))
             (<= (set::cardinality certs)
                 (set::cardinality vals)))
    :enable cardinality-of-authors-when-same-round-and-unequiv))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk certificate-sets-unequivocalp ((certs1 certificate-setp)
                                          (certs2 certificate-setp))
  :returns (yes/no booleanp)
  :short "Check if two sets of certificates have equal certificates
          for the same author and round."
  :long
  (xdoc::topstring
   (xdoc::p
    "The two sets do not need to be equal,
     but if they both have a certificate with a certain author and round,
     that must be the same certificate in both sets."))
  (forall (cert1 cert2)
          (implies (and (set::in cert1 certs1)
                        (set::in cert2 certs2)
                        (equal (certificate->author cert1)
                               (certificate->author cert2))
                        (equal (certificate->round cert1)
                               (certificate->round cert2)))
                   (equal cert1 cert2)))

  ///

  (defruled certificate-sets-unequivocalp-when-subsets
    (implies (and (certificate-sets-unequivocalp certs1 certs2)
                  (set::subset sub-certs1 certs1)
                  (set::subset sub-certs2 certs2))
             (certificate-sets-unequivocalp sub-certs1 sub-certs2))
    :expand (certificate-sets-unequivocalp sub-certs1 sub-certs2)
    :enable set::expensive-rules
    :use (:instance certificate-sets-unequivocalp-necc
                    (cert1 (mv-nth 0 (certificate-sets-unequivocalp-witness
                                      sub-certs1 sub-certs2)))
                    (cert2 (mv-nth 1 (certificate-sets-unequivocalp-witness
                                      sub-certs1 sub-certs2)))))

  (defruled certificate-set-unequivocalp-of-intersect
    (implies (certificate-sets-unequivocalp certs1 certs2)
             (certificate-set-unequivocalp (set::intersect certs1 certs2)))
    :expand (certificate-set-unequivocalp (set::intersect certs1 certs2))
    :use (:instance certificate-sets-unequivocalp-necc
                    (cert1
                     (mv-nth 0 (certificate-set-unequivocalp-witness
                                (intersect certs1 certs2))))
                    (cert2
                     (mv-nth 1 (certificate-set-unequivocalp-witness
                                (intersect certs1 certs2)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled certificate-set-unequivocalp-of-union
  :short "If two sets of unequivocal certificates
          have equal certificates for the same author and round,
          their union is an unequivocal set."
  (implies (and (certificate-set-unequivocalp certs1)
                (certificate-set-unequivocalp certs2)
                (certificate-sets-unequivocalp certs1 certs2))
           (certificate-set-unequivocalp (set::union certs1 certs2)))
  :expand (certificate-set-unequivocalp (set::union certs1 certs2))
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
                                     (union certs1 certs2))))))
  :enable set::expensive-rules)
