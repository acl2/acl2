; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "general-category")
(include-book "range-operations")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ general-category-across-versions
  :parents (general-category-property)
  :short "The code points whose @('General_Category')
          is not the same in two versions of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode Standard does not promise that
     the @('General_Category') of a character stays the same.
     Its stability policies [Stability] promise this
     for some properties only, such as the normalization forms
     (see @(see normalization-across-versions));
     the @('General_Category') of a character
     is corrected from time to time.
     For example, U+0295 LATIN LETTER PHARYNGEAL VOICED FRICATIVE
     is a @('Lowercase_Letter') (abbreviated @('Ll')) in Unicode 16.0.0
     and an @('Other_Letter') (abbreviated @('Lo')) in Unicode 17.0.0.")
   (xdoc::p
    "So, in place of a theorem,
     we define the list of the ranges of the code points
     whose @('General_Category') is not the same in two versions,
     and we prove that a code point is in those ranges
     exactly when its two values differ.
     Most of those code points are not assigned in the earlier version,
     so their value there is @('Unassigned') (abbreviated @('Cn')):
     these are the code points that the later version adds.
     The others are the changes to existing characters,
     which are what a model that depends on the @('General_Category')
     has to look at when it moves to a later version;
     we define their list too.")
   (xdoc::p
    "The lists are computed with the @(see range-operations),
     from the ranges of each of the thirty values in the two versions;
     the theorems follow from the theorems about those operations.
     The same operations compare any two lists of ranges,
     for instance the ranges of a property in two versions."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define general-category-list-changes ((gcs general-category-listp)
                                       (ver1 versionp)
                                       (ver2 versionp))
  :returns (ranges range-listp)
  :short "The code points that have
          one of the given values of @('General_Category')
          in a version of Unicode,
          and not the same value in another version."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each value of the list, these are the code points
     that are in the ranges of the value in the first version
     and not in its ranges in the second version.
     The result is in normal form
     (see @(tsee ranges-normalized-p))."))
  (cond ((endp gcs) nil)
        (t (ranges-union
            (ranges-difference (general-category-ranges (car gcs) ver1)
                               (general-category-ranges (car gcs) ver2))
            (general-category-list-changes (cdr gcs) ver1 ver2))))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule code-point-in-general-category-list-changes
    (equal (code-point-in-ranges-p
            cp
            (general-category-list-changes gcs ver1 ver2))
           (and (member-equal (code-point-general-category cp ver1)
                              (general-category-list-fix gcs))
                (not (equal (code-point-general-category cp ver1)
                            (code-point-general-category cp ver2)))))
    :induct t
    :enable (code-point-in-general-category-ranges
             member-equal
             not))

  (defrule ranges-normalized-p-of-general-category-list-changes
    (ranges-normalized-p (general-category-list-changes gcs ver1 ver2))
    :induct t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define general-category-changes ((ver1 versionp) (ver2 versionp))
  :returns (ranges range-listp)
  :short "The code points whose @('General_Category')
          is not the same in two versions of Unicode,
          as a list of ranges."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is in normal form
     (see @(tsee ranges-normalized-p)).
     It includes the code points that are assigned in one of the versions
     and not in the other;
     see @(tsee general-category-changes-of-assigned) for the others.
     The number of the code points is the @(tsee range-list-size)
     of the result."))
  (general-category-list-changes (general-category-values) ver1 ver2)
  :hooks (:fix)

  ///

  (defrule code-point-in-general-category-changes
    (equal (code-point-in-ranges-p cp (general-category-changes ver1 ver2))
           (not (equal (code-point-general-category cp ver1)
                       (code-point-general-category cp ver2)))))

  (defrule ranges-normalized-p-of-general-category-changes
    (ranges-normalized-p (general-category-changes ver1 ver2))))

;;;;;;;;;;;;;;;;;;;;

(define general-category-changes-of-assigned ((ver1 versionp) (ver2 versionp))
  :returns (ranges range-listp)
  :short "The code points that are assigned in a version of Unicode
          and whose @('General_Category') is not the same in another version,
          as a list of ranges."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code points of @(tsee general-category-changes)
     that are assigned in the first version (see @(tsee assigned-p)).
     If the first version is the earlier one,
     they are assigned in both versions,
     and these are the changes to existing characters.
     The result is in normal form
     (see @(tsee ranges-normalized-p))."))
  (ranges-difference
   (general-category-changes ver1 ver2)
   (general-category-ranges (general-category-unassigned) ver1))
  :hooks (:fix)

  ///

  (defrule code-point-in-general-category-changes-of-assigned
    (equal (code-point-in-ranges-p
            cp
            (general-category-changes-of-assigned ver1 ver2))
           (and (assigned-p cp ver1)
                (not (equal (code-point-general-category cp ver1)
                            (code-point-general-category cp ver2)))))
    :enable assigned-p-in-terms-of-ranges
    :disable ((:e general-category-unassigned)))

  (defrule ranges-normalized-p-of-general-category-changes-of-assigned
    (ranges-normalized-p (general-category-changes-of-assigned ver1 ver2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection general-category-changes-theorems
  :short "Theorems about the changes of @('General_Category')
          between versions of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "No code point changes between a version and itself.
     A code point whose @('General_Category') is not in the list of changes
     has the same value in the two versions:
     this is how a model shows that a set of code points it depends on
     is not affected by a change of version."))

  (defrule general-category-changes-of-same-version
    (equal (general-category-changes ver ver)
           nil)
    :disable (code-point-in-ranges-p-of-min-of-car-when-ranges-normalized-p
              code-point-in-general-category-changes)
    :use ((:instance
           code-point-in-ranges-p-of-min-of-car-when-ranges-normalized-p
           (ranges (general-category-changes ver ver)))
          (:instance
           code-point-in-general-category-changes
           (cp (range->min (car (general-category-changes ver ver))))
           (ver1 ver)
           (ver2 ver))))

  (defruled code-point-general-category-when-not-in-changes
    (implies (not (code-point-in-ranges-p
                   cp
                   (general-category-changes ver1 ver2)))
             (equal (code-point-general-category cp ver2)
                    (code-point-general-category cp ver1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection general-category-stability
  :short "The @('General_Category') of a code point
          that is assigned in a version of Unicode
          is the same in every later version,
          with one exception."
  :long
  (xdoc::topstring
   (xdoc::p
    "In the supported versions, in the order of @(tsee version<=),
     the exception is U+0295 LATIN LETTER PHARYNGEAL VOICED FRICATIVE:
     see @(see general-category-across-versions).
     This is a fact about these versions,
     not a promise of the Unicode Standard.
     We prove it by evaluation, for each pair of versions:
     the list of @(tsee general-category-changes-of-assigned)
     has no other code point.
     So when a version is added
     that changes the @('General_Category') of another character,
     this theorem fails,
     and the other character has to be added to its statement.")
   (xdoc::p
    "The rule is disabled by default:
     it has a version in its hypotheses
     that is not in its left side.")
   (xdoc::p
    "What the standard does promise about the @('General_Category')
     [Stability, Property Value Stability]
     is that no value is added to the thirty values
     (see @(tsee general-category-values)),
     and that the code points of three of the values never change:
     @('Control'), @('Private_Use') and @('Surrogate'),
     abbreviated @('Cc'), @('Co') and @('Cs').
     The last three theorems say this of the supported versions."))

  (defrulel changes-of-assigned-within-exceptions
    (implies (version<= (version-fix ver1) (version-fix ver2))
             (ranges-within-ranges-p
              (general-category-changes-of-assigned (version-fix ver1)
                                                    (version-fix ver2))
              (list (range #x295 #x295))))
    :rule-classes nil
    :enable (version-fix-in-terms-of-version-case
             version<=
             version-rank))

  (defruled code-point-general-category-of-later-version
    (implies (and (version<= ver1 ver2)
                  (assigned-p cp ver1)
                  (not (equal (code-point-fix cp) #x295)))
             (equal (code-point-general-category cp ver2)
                    (code-point-general-category cp ver1)))
    :enable (code-point-in-ranges-p
             code-point-in-range-p)
    :disable code-point-in-general-category-changes-of-assigned
    :use (changes-of-assigned-within-exceptions
          code-point-in-general-category-changes-of-assigned
          (:instance code-point-in-ranges-p-when-ranges-within-ranges-p
                     (subs (general-category-changes-of-assigned ver1 ver2))
                     (sups (list (range #x295 #x295))))))

  (defrule general-category-control-ranges-same-in-all-versions
    (equal (general-category-ranges (general-category-control) ver1)
           (general-category-ranges (general-category-control) ver2))
    :rule-classes nil
    :enable (general-category-ranges
             general-category-runs))

  (defrule general-category-private-use-ranges-same-in-all-versions
    (equal (general-category-ranges (general-category-private-use) ver1)
           (general-category-ranges (general-category-private-use) ver2))
    :rule-classes nil
    :enable (general-category-ranges
             general-category-runs))

  (defrule general-category-surrogate-ranges-same-in-all-versions
    (equal (general-category-ranges (general-category-surrogate) ver1)
           (general-category-ranges (general-category-surrogate) ver2))
    :rule-classes nil
    :enable (general-category-ranges
             general-category-runs)))
