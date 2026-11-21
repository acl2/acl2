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
(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")
(include-book "data/v18.0.0/prop-list")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ white-space
  :parents (unicode)
  :short "The @('White_Space') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the property of the characters that are spaces
     or that separate lines or paragraphs in ordinary text
     [UAX #44, Table 9].
     There are twenty-five of them:
     the ASCII space and the five ASCII control characters
     from the tabulation to the carriage return,
     the next-line control character,
     the no-break space and sixteen other spaces,
     and the line and paragraph separators.
     We take the property from the file @('PropList.txt')
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "This is not the property @('Pattern_White_Space')
     (see @(see pattern-white-space)),
     which is for the white space of programming languages
     and of other formal notations,
     and which never changes.
     @('White_Space') has the spaces that the other does not have,
     such as U+00A0 NO-BREAK SPACE and U+3000 IDEOGRAPHIC SPACE.
     @('Pattern_White_Space') has two characters that are not spaces:
     U+200E LEFT-TO-RIGHT MARK and U+200F RIGHT-TO-LEFT MARK.
     See @(see white-space-relations) for the theorems that relate
     @('White_Space') to @('Pattern_White_Space')
     and to the @('General_Category') property.")
   (xdoc::p
    "The property is the same in all the supported versions:
     see the theorem @('white-space-p-alt-def').
     The Unicode stability policies do not promise that,
     so a later version could add a space."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define white-space-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('White_Space') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *white-space-v16.0.0*
                :v17.0.0 *white-space-v17.0.0*
                :v18.0.0 *white-space-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define white-space-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('White_Space') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (white-space-ranges ver))
  :hooks (:fix)

  ///

  (defruled white-space-p-alt-def
    (equal (white-space-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (and (<= #x0009 cp) ; CHARACTER TABULATION, LINE FEED,
                      (<= cp #x000D)) ; LINE TABULATION, FORM FEED,
                                      ; CARRIAGE RETURN
                 (equal cp #x0020) ; SPACE
                 (equal cp #x0085) ; NEXT LINE
                 (equal cp #x00A0) ; NO-BREAK SPACE
                 (equal cp #x1680) ; OGHAM SPACE MARK
                 (and (<= #x2000 cp) ; EN QUAD to HAIR SPACE:
                      (<= cp #x200A)) ; eleven spaces of fixed widths
                 (equal cp #x2028) ; LINE SEPARATOR
                 (equal cp #x2029) ; PARAGRAPH SEPARATOR
                 (equal cp #x202F) ; NARROW NO-BREAK SPACE
                 (equal cp #x205F) ; MEDIUM MATHEMATICAL SPACE
                 (equal cp #x3000)))) ; IDEOGRAPHIC SPACE
    :enable (white-space-ranges
             code-point-in-range-p))

  (defrule white-space-p-same-in-all-versions
    (equal (white-space-p cp ver1)
           (white-space-p cp ver2))
    :rule-classes nil
    :enable white-space-p-alt-def)

  (defrule scalar-value-p-when-white-space-p
    (implies (and (white-space-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (white-space-p-alt-def scalar-value-p-alt-def)
    :disable (white-space-p scalar-value-p)))
