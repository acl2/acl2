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
(include-book "general-category-tables")

(include-book "data/v16.0.0/derived-general-category")
(include-book "data/v17.0.0/derived-general-category")
(include-book "data/v18.0.0/derived-general-category")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ general-category-property
  :parents (unicode)
  :short "The @('General_Category') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This property classifies every code point
     as a letter, a mark, a number, a punctuation mark, a symbol,
     a separator, or one of five other kinds,
     with finer distinctions within each:
     see @(tsee general-category) for its thirty values.
     Many other properties are derived from it,
     and several programming languages
     define their identifiers or their white space in terms of it.")
   (xdoc::p
    "We take the property from the file
     @('extracted/DerivedGeneralCategory.txt')
     of the Unicode Character Database, for each supported version.
     That file lists every code point.
     The generator of the tables checks it against
     the file @('UnicodeData.txt'),
     which gives the value for the code points
     that have one other than @('Unassigned').")
   (xdoc::p
    "The property is not stable:
     a new version of Unicode assigns code points
     that were @('Unassigned'),
     and now and then changes the value of an assigned one.
     For example U+0295 LATIN LETTER PHARYNGEAL VOICED FRICATIVE
     is a @('Lowercase_Letter') in Unicode 16.0.0
     and an @('Other_Letter') in Unicode 17.0.0.")
   (xdoc::p
    "The function @(tsee code-point-general-category)
     gives the value of a code point,
     and @(tsee general-category-ranges)
     gives the code points that have a value, as a list of ranges.
     The theorem @('code-point-in-general-category-ranges')
     says that the two agree."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define general-category-runs ((ver versionp))
  :returns (runs general-category-run-listp)
  :short "The @('General_Category') of every code point,
          as a list of runs, in a version of Unicode."
  (version-case ver
                :v16.0.0 *general-category-v16.0.0*
                :v17.0.0 *general-category-v17.0.0*
                :v18.0.0 *general-category-v18.0.0*)
  :hooks (:fix)

  ///

  (defrule general-category-runs-cover-all-code-points
    (general-category-run-list-covers-p 0 #x10FFFF
                                        (general-category-runs ver))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define code-point-general-category ((cp code-point-p) (ver versionp))
  :returns (gc general-category-p)
  :short "The @('General_Category') of a code point,
          in a version of Unicode."
  (general-category-run-list-lookup cp (general-category-runs ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-ranges ((gc general-category-p) (ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have a given @('General_Category'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The ranges are in increasing order and do not overlap.
     They are computed from the list of runs at each call,
     by going through the whole list."))
  (general-category-run-list-ranges gc (general-category-runs ver))
  :hooks (:fix)

  ///

  (defruled code-point-in-general-category-ranges
    (equal (code-point-in-ranges-p cp (general-category-ranges gc ver))
           (equal (code-point-general-category cp ver)
                  (general-category-fix gc)))
    :enable (code-point-general-category
             code-point-in-general-category-run-list-ranges))

  (defruled equal-of-code-point-general-category
    (equal (equal (code-point-general-category cp ver) gc)
           (and (general-category-p gc)
                (code-point-in-ranges-p cp (general-category-ranges gc ver))))
    :enable code-point-in-general-category-ranges
    :disable general-category-ranges))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define assigned-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is assigned, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is not @('Unassigned'),
     which is abbreviated @('Cn') [UAX #44, Table 12].
     In this sense the surrogates and the private-use code points
     are assigned, since they have values of their own,
     and the noncharacters are not:
     the code points that are not assigned
     are the noncharacters and the code points
     that are reserved for future assignment.")
   (xdoc::p
    "A code point that is assigned in a version of Unicode
     is assigned in every later version."))
  (not (general-category-case (code-point-general-category cp ver)
                              :unassigned))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist assigned-listp (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check if all the code points of a list are assigned,
          in a version of Unicode."
  (assigned-p x ver)

  ///

  (fty::deffixequiv assigned-listp
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (assigned-listp x ver)
             :in-theory (enable assigned-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection general-category-theorems
  :short "Theorems about @('General_Category')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code points whose value is @('Surrogate')
     are exactly the surrogates.")
   (xdoc::p
    "This is proved by evaluation on the tables, for each version:
     so adding a version checks it for that version.
     Theorems that relate this property to other properties
     are in @(see property-relations)."))

  (defrulel surrogate-ranges
    (equal (general-category-ranges (general-category-surrogate) ver)
           (list (range #xD800 #xDFFF)))
    :enable (general-category-ranges general-category-runs))

  (defrulel general-category-kind-is-surrogate
    (implies (general-category-p gc)
             (equal (equal (general-category-kind gc) :surrogate)
                    (equal gc (general-category-surrogate))))
    :enable equal-of-general-category-surrogate
    :disable ((:e general-category-surrogate)))

  (defruled general-category-surrogate-iff-surrogate-p
    (equal (general-category-case (code-point-general-category cp ver)
                                  :surrogate)
           (surrogate-p cp))
    :enable (equal-of-code-point-general-category
             surrogate-p-alt-def
             code-point-in-range-p)
    :disable ((:e general-category-surrogate)
              surrogate-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection assigned-across-versions
  :short "A code point that is assigned in a version of Unicode
          is assigned in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee assigned-p), and @(tsee version<=) for the order.
     This is a promise of the Unicode Standard:
     once a character is encoded, it is not moved or removed
     [Stability, Encoding Stability].
     Here it is a theorem about the supported versions,
     proved by evaluation on the tables, for each pair of versions:
     each range of unassigned code points of the later version
     is within such a range of the earlier one.")
   (xdoc::p
    "The first theorem says that a code point is assigned
     exactly when it is not in the ranges of the code points
     whose @('General_Category') is @('Unassigned').
     The @('General_Category') of an assigned code point
     can change from a version to a later one:
     see @(see general-category-across-versions)."))

  (defrulel general-category-kind-is-unassigned
    (implies (general-category-p gc)
             (equal (equal (general-category-kind gc) :unassigned)
                    (equal gc (general-category-unassigned))))
    :enable equal-of-general-category-unassigned
    :disable ((:e general-category-unassigned)))

  (defruled assigned-p-in-terms-of-ranges
    (equal (assigned-p cp ver)
           (not (code-point-in-ranges-p
                 cp
                 (general-category-ranges (general-category-unassigned)
                                          ver))))
    :enable (assigned-p
             equal-of-code-point-general-category)
    :disable ((:e general-category-unassigned)))

  (defrulel unassigned-ranges-within-ranges-of-earlier-version
    (implies (version<= ver1 ver2)
             (ranges-within-ranges-p
              (general-category-ranges (general-category-unassigned) ver2)
              (general-category-ranges (general-category-unassigned) ver1)))
    :rule-classes :forward-chaining
    :enable (version<=
             version-rank
             general-category-ranges
             general-category-runs))

  (defruled assigned-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1))
             (assigned-p cp ver2))
    :enable (assigned-p-in-terms-of-ranges
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-unassigned)))

  (defruled assigned-listp-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-listp cps ver1))
             (assigned-listp cps ver2))
    :induct (len cps)
    :enable (assigned-listp
             assigned-p-of-later-version
             len)))
