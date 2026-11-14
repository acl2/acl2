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

(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pattern-white-space
  :parents (unicode)
  :short "The @('Pattern_White_Space') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the property that [UAX #31] recommends
     for the white space of programming languages
     and of other formal notations.
     We take it from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "The Unicode stability policies say that
     this property does not change,
     and indeed it is the same in all the supported versions:
     see the theorem @('pattern-white-space-p-alt-def').
     Its version argument is there for uniformity,
     and so that the claim is checked rather than assumed
     when a version is added."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pattern-white-space-set ((ver versionp))
  :returns (set range-set-p)
  :short "The set of the code points
          that have the @('Pattern_White_Space') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *pattern-white-space-v16.0.0*
                :v17.0.0 *pattern-white-space-v17.0.0*))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pattern-white-space-p ((cp natp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Pattern_White_Space') property,
          in a version of Unicode."
  (in-range-set-p cp (pattern-white-space-set ver))

  ///

  (defruled pattern-white-space-p-alt-def
    (equal (pattern-white-space-p cp ver)
           (b* ((cp (nfix cp)))
             (or (and (<= #x0009 cp) ; CHARACTER TABULATION, LINE FEED,
                      (<= cp #x000D)) ; LINE TABULATION, FORM FEED,
                                      ; CARRIAGE RETURN
                 (equal cp #x0020) ; SPACE
                 (equal cp #x0085) ; NEXT LINE
                 (equal cp #x200E) ; LEFT-TO-RIGHT MARK
                 (equal cp #x200F) ; RIGHT-TO-LEFT MARK
                 (equal cp #x2028) ; LINE SEPARATOR
                 (equal cp #x2029)))) ; PARAGRAPH SEPARATOR
    :enable (pattern-white-space-set in-range-set-p))

  (defrule scalar-value-p-when-pattern-white-space-p
    (implies (and (pattern-white-space-p cp ver)
                  (natp cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (pattern-white-space-p-alt-def scalar-value-p-alt-def nfix)
    :disable (pattern-white-space-p scalar-value-p)))
