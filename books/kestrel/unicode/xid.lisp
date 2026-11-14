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
(include-book "range-sets")

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
    "The functions are defined on all natural numbers,
     and are false on those that are not code points.
     No surrogate has either property,
     so a code point that has one of them is a scalar value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-start-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points that have the @('XID_Start') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-start-v16.0.0*
                :v17.0.0 *xid-start-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points that have the @('XID_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-continue-v16.0.0*
                :v17.0.0 *xid-continue-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define xid-start-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('XID_Start') property,
          in a version of Unicode."
  (in-range-set-p cp (xid-start-set ver)))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('XID_Continue') property,
          in a version of Unicode."
  (in-range-set-p cp (xid-continue-set ver)))

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

  (defrule xid-start-set-subset-of-xid-continue-set
    (range-set-subset-p (xid-start-set ver) (xid-continue-set ver))
    :enable (xid-start-set xid-continue-set))

  (defrule xid-continue-set-subset-of-scalar-values
    (range-set-subset-p (xid-continue-set ver) *scalar-value-range-set*)
    :enable xid-continue-set)

  (defrule xid-continue-p-when-xid-start-p
    (implies (xid-start-p cp ver)
             (xid-continue-p cp ver))
    :enable (xid-start-p xid-continue-p)
    :use (:instance in-range-set-p-when-range-set-subset-p
                    (sub (xid-start-set ver))
                    (sup (xid-continue-set ver))))

  (defrule scalar-value-p-when-xid-continue-p
    (implies (and (xid-continue-p cp ver)
                  (natp cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (xid-continue-p
             scalar-value-p-when-in-scalar-value-range-set)
    :use (:instance in-range-set-p-when-range-set-subset-p
                    (sub (xid-continue-set ver))
                    (sup *scalar-value-range-set*)))

  (defrule scalar-value-p-when-xid-start-p
    (implies (and (xid-start-p cp ver)
                  (natp cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :use (xid-continue-p-when-xid-start-p
          scalar-value-p-when-xid-continue-p)
    :disable (xid-continue-p-when-xid-start-p
              scalar-value-p-when-xid-continue-p))

  (defruled xid-start-p-when-ascii
    (implies (and (natp cp)
                  (< cp #x80))
             (equal (xid-start-p cp ver)
                    (or (and (<= (char-code #\A) cp)
                             (<= cp (char-code #\Z)))
                        (and (<= (char-code #\a) cp)
                             (<= cp (char-code #\z))))))
    :enable (xid-start-p
             xid-start-set
             in-range-set-p
             not-in-range-set-p-when-below-first
             nfix))

  (defruled xid-continue-p-when-ascii
    (implies (and (natp cp)
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
             xid-continue-set
             in-range-set-p
             not-in-range-set-p-when-below-first
             nfix)))
