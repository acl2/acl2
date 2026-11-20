; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "id")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ id-compat-math
  :parents (unicode)
  :short "The @('ID_Compat_Math_Start')
          and @('ID_Compat_Math_Continue') properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "These two properties list the characters
     that the mathematical compatibility notation profile
     of [UAX #31, Section 7.1] adds to identifiers:
     @('ID_Compat_Math_Start') has the characters
     that the profile lets an identifier start with,
     and @('ID_Compat_Math_Continue') those it lets one continue with.
     In these names @('ID') is short for `identifier',
     and @('Compat') for `compatibility'.")
   (xdoc::p
    "The first property has thirteen code points:
     the partial differential sign, the nabla and the infinity sign,
     and the styled forms of the first two
     among the mathematical alphanumeric symbols.
     The second has those and thirty more:
     the superscript and subscript digits, signs and parentheses.
     None of them has @('ID_Continue'),
     so the profile only adds code points to the default identifiers.")
   (xdoc::p
    "We take the properties from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.
     They are the same in all the supported versions:
     see the theorems with names ending in @('alt-def'),
     which list their ranges.
     The profile itself, as a predicate on lists of code points,
     is not defined here."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-compat-math-start-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('ID_Compat_Math_Start') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *id-compat-math-start-v16.0.0*
                :v17.0.0 *id-compat-math-start-v17.0.0*
                :v18.0.0 *id-compat-math-start-v18.0.0*)
  :hooks (:fix)

  ///

  (defruled id-compat-math-start-ranges-alt-def
    (equal (id-compat-math-start-ranges ver)
           (list (range #x2202 #x2202) ; PARTIAL DIFFERENTIAL
                 (range #x2207 #x2207) ; NABLA
                 (range #x221E #x221E) ; INFINITY
                 (range #x1D6C1 #x1D6C1) ; MATHEMATICAL BOLD NABLA
                 (range #x1D6DB #x1D6DB) ; ... BOLD PARTIAL DIFFERENTIAL
                 (range #x1D6FB #x1D6FB) ; ... ITALIC NABLA
                 (range #x1D715 #x1D715) ; ... ITALIC PARTIAL DIFFERENTIAL
                 (range #x1D735 #x1D735) ; ... BOLD ITALIC NABLA
                 (range #x1D74F #x1D74F) ; ... BOLD ITALIC PARTIAL ...
                 (range #x1D76F #x1D76F) ; ... SANS-SERIF BOLD NABLA
                 (range #x1D789 #x1D789) ; ... SANS-SERIF BOLD PARTIAL ...
                 (range #x1D7A9 #x1D7A9) ; ... SANS-SERIF BOLD ITALIC NABLA
                 (range #x1D7C3 #x1D7C3)))) ; ... BOLD ITALIC PARTIAL ...

  (defrule id-compat-math-start-ranges-same-in-all-versions
    (equal (id-compat-math-start-ranges ver1)
           (id-compat-math-start-ranges ver2))
    :rule-classes nil
    :enable id-compat-math-start-ranges-alt-def
    :disable id-compat-math-start-ranges))

;;;;;;;;;;;;;;;;;;;;

(define id-compat-math-continue-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('ID_Compat_Math_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *id-compat-math-continue-v16.0.0*
                :v17.0.0 *id-compat-math-continue-v17.0.0*
                :v18.0.0 *id-compat-math-continue-v18.0.0*)
  :hooks (:fix)

  ///

  (defruled id-compat-math-continue-ranges-alt-def
    (equal (id-compat-math-continue-ranges ver)
           (list* (range #x00B2 #x00B3) ; SUPERSCRIPT TWO and THREE
                  (range #x00B9 #x00B9) ; SUPERSCRIPT ONE
                  (range #x2070 #x2070) ; SUPERSCRIPT ZERO
                  (range #x2074 #x207E) ; SUPERSCRIPT FOUR to PARENTHESIS
                  (range #x2080 #x208E) ; SUBSCRIPT ZERO to PARENTHESIS
                  (id-compat-math-start-ranges ver)))
    :enable id-compat-math-start-ranges)

  (defrule id-compat-math-continue-ranges-same-in-all-versions
    (equal (id-compat-math-continue-ranges ver1)
           (id-compat-math-continue-ranges ver2))
    :rule-classes nil
    :enable (id-compat-math-continue-ranges-alt-def
             id-compat-math-start-ranges-alt-def)
    :disable (id-compat-math-continue-ranges
              id-compat-math-start-ranges)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-compat-math-start-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('ID_Compat_Math_Start') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (id-compat-math-start-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define id-compat-math-continue-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has
          the @('ID_Compat_Math_Continue') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (id-compat-math-continue-ranges ver))
  :hooks (:fix)

  ///

  (defrule id-compat-math-continue-p-when-id-compat-math-start-p
    (implies (id-compat-math-start-p cp ver)
             (id-compat-math-continue-p cp ver))
    :enable (id-compat-math-start-p
             id-compat-math-continue-ranges-alt-def)
    :disable (id-compat-math-continue-ranges
              id-compat-math-start-ranges)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection id-compat-math-theorems
  :short "No code point of @('ID_Compat_Math_Continue')
          has @('ID_Continue')."
  :long
  (xdoc::topstring
   (xdoc::p
    "So none has @('XID_Continue'), @('ID_Start') or @('XID_Start') either:
     the characters of the two properties
     are not characters of the default identifiers.
     This is proved by evaluation on the tables, for each version."))

  (defrulel id-compat-math-continue-ranges-disjoint-from-id-continue-ranges
    (ranges-disjoint-from-ranges-p (id-compat-math-continue-ranges ver)
                                   (id-continue-ranges ver))
    :enable (id-compat-math-continue-ranges
             id-continue-ranges))

  (defrule not-id-continue-p-when-id-compat-math-continue-p
    (implies (id-compat-math-continue-p cp ver)
             (not (id-continue-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (id-compat-math-continue-p
             id-continue-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p))

  (defrule not-xid-continue-p-when-id-compat-math-continue-p
    (implies (id-compat-math-continue-p cp ver)
             (not (xid-continue-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :disable (id-compat-math-continue-p
              id-continue-p-when-xid-continue-p)
    :use id-continue-p-when-xid-continue-p))
