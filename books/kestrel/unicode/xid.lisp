; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "versions")
(include-book "ranges")

(include-book "data/v16.0.0/derived-core-properties")
(include-book "data/v17.0.0/derived-core-properties")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ xid
  :parents (unicode)
  :short "The @('XID_Start') and @('XID_Continue') properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the properties that the default identifier syntax
     of [UAX #31] recommends for programming languages:
     an identifier consists of a code point with @('XID_Start')
     followed by any number of code points with @('XID_Continue').
     (Languages adjust this;
     many also let an identifier start with an underscore,
     which has @('XID_Continue') but not @('XID_Start').)
     Unlike @('ID_Start') and @('ID_Continue'),
     the @('XID') properties are closed under
     the Unicode normalization forms:
     normalizing an identifier gives an identifier.")
   (xdoc::p
    "Both are derived properties.
     We take them from the file @('DerivedCoreProperties.txt')
     of the Unicode Character Database, for each supported version;
     we do not recompute them from the properties they derive from.")
   (xdoc::p
    "No surrogate has either property,
     so a code point that has one of them is a scalar value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-start-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('XID_Start') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-start-v16.0.0*
                :v17.0.0 *xid-start-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('XID_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-continue-v16.0.0*
                :v17.0.0 *xid-continue-v17.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-start-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('XID_Start') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (xid-start-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('XID_Continue') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (xid-continue-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection xid-theorems
  :short "Theorems about @('XID_Start') and @('XID_Continue')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every code point that can start an identifier can continue one.
     Every code point that can continue an identifier is a scalar value.
     Among the ASCII code points,
     the ones that can start an identifier are the letters,
     and the ones that can continue an identifier are
     the letters, the digits and the underscore.")
   (xdoc::p
    "These are proved by evaluation on the tables, for each version:
     so adding a version checks them for that version."))

  (defrule xid-start-ranges-within-xid-continue-ranges
    (ranges-within-ranges-p (xid-start-ranges ver)
                            (xid-continue-ranges ver))
    :enable (xid-start-ranges xid-continue-ranges))

  (defrule xid-continue-ranges-within-scalar-value-ranges
    (ranges-within-ranges-p (xid-continue-ranges ver)
                            (scalar-value-ranges))
    :enable (xid-continue-ranges (:e scalar-value-ranges)))

  (defrule xid-continue-p-when-xid-start-p
    (implies (xid-start-p cp ver)
             (xid-continue-p cp ver))
    :enable (xid-start-p
             xid-continue-p)
    :use (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                    (subs (xid-start-ranges ver))
                    (sups (xid-continue-ranges ver))))

  (defrule scalar-value-p-when-xid-continue-p
    (implies (and (xid-continue-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (xid-continue-p
             scalar-value-p-when-code-point-in-scalar-value-ranges)
    :use (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                    (subs (xid-continue-ranges ver))
                    (sups (scalar-value-ranges))))

  (defrule scalar-value-p-when-xid-start-p
    (implies (and (xid-start-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :use (xid-continue-p-when-xid-start-p
          scalar-value-p-when-xid-continue-p)
    :disable (xid-continue-p-when-xid-start-p
              scalar-value-p-when-xid-continue-p))

  ;; The ASCII code points that have, and that do not have, XID_Start:

  (defrulel ascii-letters-within-xid-start-ranges
    (ranges-within-ranges-p (list (range #x41 #x5A)
                                  (range #x61 #x7A))
                            (xid-start-ranges ver))
    :enable xid-start-ranges)

  (defrulel ascii-non-letters-disjoint-from-xid-start-ranges
    (ranges-disjoint-from-ranges-p (list (range #x00 #x40)
                                         (range #x5B #x60)
                                         (range #x7B #x7F))
                                   (xid-start-ranges ver))
    :enable xid-start-ranges)

  (defruled xid-start-p-when-ascii
    (implies (and (code-point-p cp)
                  (< cp #x80))
             (equal (xid-start-p cp ver)
                    (or (and (<= (char-code #\A) cp)
                             (<= cp (char-code #\Z)))
                        (and (<= (char-code #\a) cp)
                             (<= cp (char-code #\z))))))
    :enable (xid-start-p
             code-point-in-range-p
             code-point-p)
    :use (ascii-letters-within-xid-start-ranges
          ascii-non-letters-disjoint-from-xid-start-ranges
          (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                     (subs (list (range #x41 #x5A)
                                 (range #x61 #x7A)))
                     (sups (xid-start-ranges ver)))
          (:instance
           not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p
           (xs (list (range #x00 #x40)
                     (range #x5B #x60)
                     (range #x7B #x7F)))
           (ys (xid-start-ranges ver)))))

  ;; The ASCII code points that have, and that do not have, XID_Continue:

  (defrulel ascii-letters-digits-underscore-within-xid-continue-ranges
    (ranges-within-ranges-p (list (range #x30 #x39)
                                  (range #x41 #x5A)
                                  (range #x5F #x5F)
                                  (range #x61 #x7A))
                            (xid-continue-ranges ver))
    :enable xid-continue-ranges)

  (defrulel ascii-others-disjoint-from-xid-continue-ranges
    (ranges-disjoint-from-ranges-p (list (range #x00 #x2F)
                                         (range #x3A #x40)
                                         (range #x5B #x5E)
                                         (range #x60 #x60)
                                         (range #x7B #x7F))
                                   (xid-continue-ranges ver))
    :enable xid-continue-ranges)

  (defruled xid-continue-p-when-ascii
    (implies (and (code-point-p cp)
                  (< cp #x80))
             (equal (xid-continue-p cp ver)
                    (or (and (<= (char-code #\0) cp)
                             (<= cp (char-code #\9)))
                        (and (<= (char-code #\A) cp)
                             (<= cp (char-code #\Z)))
                        (equal cp (char-code #\_))
                        (and (<= (char-code #\a) cp)
                             (<= cp (char-code #\z))))))
    :enable (xid-continue-p
             code-point-in-range-p
             code-point-p)
    :use (ascii-letters-digits-underscore-within-xid-continue-ranges
          ascii-others-disjoint-from-xid-continue-ranges
          (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                     (subs (list (range #x30 #x39)
                                 (range #x41 #x5A)
                                 (range #x5F #x5F)
                                 (range #x61 #x7A)))
                     (sups (xid-continue-ranges ver)))
          (:instance
           not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p
           (xs (list (range #x00 #x2F)
                     (range #x3A #x40)
                     (range #x5B #x5E)
                     (range #x60 #x60)
                     (range #x7B #x7F)))
           (ys (xid-continue-ranges ver))))))
