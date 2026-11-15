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
(include-book "data/v18.0.0/derived-core-properties")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

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
                :v17.0.0 *xid-start-v17.0.0*
                :v18.0.0 *xid-start-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define xid-continue-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('XID_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *xid-continue-v16.0.0*
                :v17.0.0 *xid-continue-v17.0.0*
                :v18.0.0 *xid-continue-v18.0.0*)
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
    :rule-classes (:rewrite :forward-chaining)
    :enable (xid-start-p
             xid-continue-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule scalar-value-p-when-xid-continue-p
    (implies (and (xid-continue-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (xid-continue-p
             scalar-value-p-when-code-point-in-scalar-value-ranges
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule scalar-value-p-when-xid-start-p
    (implies (and (xid-start-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining))

  ;; The ASCII code points that have, and that do not have, XID_Start.
  ;; We check each of the 128 ASCII code points, for each version.

  (local
   (define ascii-start-ok ((cp code-point-p) (ranges range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp)))
       (equal (code-point-in-ranges-p cp ranges)
              (or (and (<= (char-code #\A) cp)
                       (<= cp (char-code #\Z)))
                  (and (<= (char-code #\a) cp)
                       (<= cp (char-code #\z))))))
     :hooks nil))

  (local
   (std::deflist ascii-start-ok-listp (x ranges)
     :guard (and (code-point-listp x)
                 (range-listp ranges))
     (ascii-start-ok x ranges)))

  (defrulel ascii-start-ok-listp-of-ascii
    (ascii-start-ok-listp (integers-from-to 0 #x7F)
                          (xid-start-ranges ver))
    :enable xid-start-ranges
    :disable ascii-start-ok-listp-of-cons)

  (defruled xid-start-p-when-ascii
    (implies (and (code-point-p cp)
                  (< cp #x80))
             (equal (xid-start-p cp ver)
                    (or (and (<= (char-code #\A) cp)
                             (<= cp (char-code #\Z)))
                        (and (<= (char-code #\a) cp)
                             (<= cp (char-code #\z))))))
    :enable (xid-start-p
             ascii-start-ok
             code-point-p)
    :disable ((:e integers-from-to))
    :use (:instance ascii-start-ok-when-member-equal-of-ascii-start-ok-listp
                    (acl2::a cp)
                    (x (integers-from-to 0 #x7F))
                    (ranges (xid-start-ranges ver))))

  ;; The ASCII code points that have, and that do not have, XID_Continue.
  ;; We check each of the 128 ASCII code points, for each version.

  (local
   (define ascii-continue-ok ((cp code-point-p) (ranges range-listp))
     :returns (yes/no booleanp)
     (b* ((cp (code-point-fix cp)))
       (equal (code-point-in-ranges-p cp ranges)
              (or (and (<= (char-code #\0) cp)
                       (<= cp (char-code #\9)))
                  (and (<= (char-code #\A) cp)
                       (<= cp (char-code #\Z)))
                  (equal cp (char-code #\_))
                  (and (<= (char-code #\a) cp)
                       (<= cp (char-code #\z))))))
     :hooks nil))

  (local
   (std::deflist ascii-continue-ok-listp (x ranges)
     :guard (and (code-point-listp x)
                 (range-listp ranges))
     (ascii-continue-ok x ranges)))

  (defrulel ascii-continue-ok-listp-of-ascii
    (ascii-continue-ok-listp (integers-from-to 0 #x7F)
                             (xid-continue-ranges ver))
    :enable xid-continue-ranges
    :disable ascii-continue-ok-listp-of-cons)

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
             ascii-continue-ok
             code-point-p)
    :disable ((:e integers-from-to))
    :use (:instance
          ascii-continue-ok-when-member-equal-of-ascii-continue-ok-listp
          (acl2::a cp)
          (x (integers-from-to 0 #x7F))
          (ranges (xid-continue-ranges ver)))))
