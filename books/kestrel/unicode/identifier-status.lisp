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
(include-book "identifier-type-tables")

(include-book "data/v16.0.0/identifier-status")
(include-book "data/v17.0.0/identifier-status")
(include-book "data/v18.0.0/identifier-status")
(include-book "data/v16.0.0/identifier-type")
(include-book "data/v17.0.0/identifier-type")
(include-book "data/v18.0.0/identifier-type")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifier-status
  :parents (unicode)
  :short "The @('Identifier_Status') and @('Identifier_Type') properties
          of Unicode Security Mechanisms."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode Technical Standard #39, Unicode Security Mechanisms,
     which we cite as [UTS #39],
     has a profile of the characters
     that are safe to allow in identifiers [UTS #39, Section 3.1].
     The @('Identifier_Status') of a code point
     is @('Allowed') if the profile has it and @('Restricted') if not.
     The @('Identifier_Type') of a code point is a set of types,
     which say why: see @(tsee identifier-type) for the twelve types.")
   (xdoc::p
    "The two properties say the same thing in two ways:
     a code point is @('Allowed') exactly when each of its types
     is @('Inclusion') or @('Recommended').
     That is a theorem here
     (@('identifier-allowed-p-in-terms-of-types')).
     The types are sets
     because a character can be restricted for more than one reason.")
   (xdoc::p
    "We take the properties from the files
     @('IdentifierStatus.txt') and @('IdentifierType.txt') of [UTS #39],
     for each supported version of Unicode.
     These are not files of the Unicode Character Database,
     but they are published for each version of Unicode.")
   (xdoc::p
    "[UTS #39] gives these properties no stability guarantee,
     and they do change:
     Unicode 16.0.0 allows 112,778 code points
     and Unicode 17.0.0 allows 33,791,
     most of the difference being ideographs
     that became @('Uncommon_Use').
     So which version an implementation uses matters more here
     than for any other property of this library.")
   (xdoc::p
    "Theorems that relate these properties to others,
     such as that no @('Allowed') code point is changed
     by Normalization Form KC,
     are in @(see identifier-type-relations)
     and @(see identifier-status-and-normalization)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-allowed-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          whose @('Identifier_Status') is @('Allowed'),
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *identifier-status-allowed-v16.0.0*
                :v17.0.0 *identifier-status-allowed-v17.0.0*
                :v18.0.0 *identifier-status-allowed-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define identifier-allowed-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the @('Identifier_Status') of a code point
          is @('Allowed'), in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The property has two values:
     if this function returns @('nil'),
     the status of the code point is @('Restricted')."))
  (code-point-in-ranges-p cp (identifier-allowed-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-type-runs ((ver versionp))
  :returns (runs identifier-type-run-listp)
  :short "The @('Identifier_Type') of every code point,
          as a list of runs, in a version of Unicode."
  (version-case ver
                :v16.0.0 *identifier-type-v16.0.0*
                :v17.0.0 *identifier-type-v17.0.0*
                :v18.0.0 *identifier-type-v18.0.0*)
  :hooks (:fix)

  ///

  (defrule identifier-type-runs-cover-all-code-points
    (identifier-type-run-list-covers-p 0 #x10FFFF
                                       (identifier-type-runs ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-identifier-types ((cp code-point-p) (ver versionp))
  :returns (types identifier-type-listp)
  :short "The @('Identifier_Type') of a code point,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is a list of types without duplicates,
     which stands for a set; it is never empty.
     The types are in the order
     of the file @('IdentifierType.txt')."))
  (identifier-type-run-list-lookup cp (identifier-type-runs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define identifier-type-ranges ((type identifier-type-p) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          whose @('Identifier_Type') contains a given type,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges are in increasing order and do not overlap.
     They are computed from the list of runs at each call,
     by going through the whole list."))
  (identifier-type-run-list-member-ranges type (identifier-type-runs ver))
  :hooks (:fix)

  ///

  (defruled code-point-in-identifier-type-ranges
    (iff (code-point-in-ranges-p cp (identifier-type-ranges type ver))
         (member-equal (identifier-type-fix type)
                       (code-point-identifier-types cp ver)))
    :enable (code-point-identifier-types
             code-point-in-identifier-type-run-list-member-ranges)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist identifier-type-list-allowed-p (x)
  :guard (identifier-type-listp x)
  :short "Check if every type of a list
          is @('Inclusion') or @('Recommended')."
  (identifier-type-allowed-p x)

  ///

  (fty::deffixequiv identifier-type-list-allowed-p
    :args ((x identifier-type-listp))
    :hints (("Goal"
             :induct (identifier-type-list-allowed-p x)
             :in-theory (enable identifier-type-list-allowed-p)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection identifier-status-theorems
  :short "A code point is @('Allowed') exactly when
          each of its types is @('Inclusion') or @('Recommended')."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is how [UTS #39, Table 1] relates the two properties.
     Here it is a theorem about the tables of the supported versions,
     which come from two files.
     The set of types of a code point is never empty.")
   (xdoc::p
    "We prove the theorem by checking, for each version,
     each run of the table of the types against the ranges of the status:
     if every type of the run is @('Inclusion') or @('Recommended'),
     the run is within one of the ranges of the @('Allowed') code points,
     and otherwise it is disjoint from all of them.
     That is a check on a few thousand runs.
     Since the runs cover every code point,
     the theorem follows by induction on the list of runs.
     So adding a version checks the two files of that version
     against each other."))

  (local
   (define runs-agree-p ((runs identifier-type-run-listp)
                         (allowed range-listp))
     :returns (yes/no booleanp)
     (or (endp runs)
         (b* (((identifier-type-run run) (car runs))
              (range (range run.min run.max)))
           (and (consp run.value)
                (if (identifier-type-list-allowed-p run.value)
                    (range-within-ranges-p range allowed)
                  (range-disjoint-from-ranges-p range allowed))
                (runs-agree-p (cdr runs) allowed))))
     :hooks nil

     ///

     (defrule consp-of-lookup-when-runs-agree-p
       (implies (runs-agree-p runs allowed)
                (consp (identifier-type-run-list-lookup cp runs)))
       :induct t
       :enable identifier-type-run-list-lookup)

     (defrulel code-point-fix-upper-bound
       (<= (code-point-fix x) #x10FFFF)
       :rule-classes :linear
       :enable (code-point-fix code-point-p))

     (defrule in-ranges-iff-lookup-allowed-when-runs-agree-p
       (implies (and (runs-agree-p runs allowed)
                     (identifier-type-run-list-covers-p min max runs)
                     (<= (code-point-fix min) (code-point-fix cp))
                     (<= (code-point-fix cp) (code-point-fix max)))
                (equal (code-point-in-ranges-p cp allowed)
                       (identifier-type-list-allowed-p
                        (identifier-type-run-list-lookup cp runs))))
       :induct (identifier-type-run-list-covers-p min max runs)
       :enable (identifier-type-run-list-covers-p
                identifier-type-run-list-lookup
                code-point-in-range-p
                code-point-p)
       :hints
       ('(:use
          ((:instance
            code-point-in-ranges-p-when-range-within-ranges-p
            (sub (range (identifier-type-run->min (car runs))
                        (identifier-type-run->max (car runs))))
            (sups allowed))
           (:instance
            not-code-point-in-ranges-p-when-range-disjoint-from-ranges-p
            (range (range (identifier-type-run->min (car runs))
                          (identifier-type-run->max (car runs))))
            (ranges allowed))))))))

  (defrulel code-point-fix-upper-bound
    (<= (code-point-fix x) #x10FFFF)
    :rule-classes :linear
    :enable (code-point-fix code-point-p))

  (defrulel runs-agree-p-of-identifier-type-runs
    (runs-agree-p (identifier-type-runs ver)
                  (identifier-allowed-ranges ver))
    :enable (identifier-type-runs
             identifier-allowed-ranges))

  (defrule consp-of-code-point-identifier-types
    (consp (code-point-identifier-types cp ver))
    :rule-classes :type-prescription
    :enable code-point-identifier-types
    :disable consp-of-lookup-when-runs-agree-p
    :use (:instance consp-of-lookup-when-runs-agree-p
                    (runs (identifier-type-runs ver))
                    (allowed (identifier-allowed-ranges ver))))

  (defruled identifier-allowed-p-in-terms-of-types
    (equal (identifier-allowed-p cp ver)
           (identifier-type-list-allowed-p
            (code-point-identifier-types cp ver)))
    :enable (identifier-allowed-p
             code-point-identifier-types)
    :disable in-ranges-iff-lookup-allowed-when-runs-agree-p
    :use (:instance in-ranges-iff-lookup-allowed-when-runs-agree-p
                    (runs (identifier-type-runs ver))
                    (allowed (identifier-allowed-ranges ver))
                    (min 0)
                    (max #x10FFFF))))
