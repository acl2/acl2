; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "xid")

(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")
(include-book "data/v18.0.0/prop-list")

(local (include-book "range-operations"))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ id-properties
  :parents (unicode)
  :short "The @('ID_Start') and @('ID_Continue') properties,
          and the two properties that list their exceptions."
  :long
  (xdoc::topstring
   (xdoc::p
    "In these names, @('ID') is short for `identifier'.
     @('ID_Start') is the property of the code points
     that can start an identifier,
     and @('ID_Continue') that of the code points that can continue one,
     in the default identifier syntax of [UAX #31, UAX31-D1].
     They are derived from the @('General_Category'),
     with two small lists of additions,
     @('Other_ID_Start') and @('Other_ID_Continue'),
     and without the characters of syntax and of white space:
     see the theorems in @(see id-relations).")
   (xdoc::p
    "[UAX #31] recommends two other properties
     for the identifiers of programming languages,
     @('XID_Start') and @('XID_Continue'),
     which are in @(see xid).
     Those are @('ID_Start') and @('ID_Continue')
     without a few code points
     whose compatibility decompositions are not identifiers.
     The theorems here say exactly which:
     23 code points for the first property and 19 for the second,
     the same in every supported version.")
   (xdoc::p
    "We take @('ID_Start') and @('ID_Continue')
     from the file @('DerivedCoreProperties.txt'),
     and @('Other_ID_Start') and @('Other_ID_Continue')
     from the file @('PropList.txt'),
     of the Unicode Character Database, for each supported version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-start-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('ID_Start') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *id-start-v16.0.0*
                :v17.0.0 *id-start-v17.0.0*
                :v18.0.0 *id-start-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define id-continue-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('ID_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *id-continue-v16.0.0*
                :v17.0.0 *id-continue-v17.0.0*
                :v18.0.0 *id-continue-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define id-start-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('ID_Start') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if it can start an identifier
     in the default identifier syntax of [UAX #31].
     See @(see id-properties) for the name of the property."))
  (code-point-in-ranges-p cp (id-start-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define id-continue-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('ID_Continue') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if it can continue an identifier
     in the default identifier syntax of [UAX #31].
     See @(see id-properties) for the name of the property."))
  (code-point-in-ranges-p cp (id-continue-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define other-id-start-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Other_ID_Start') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *other-id-start-v16.0.0*
                :v17.0.0 *other-id-start-v17.0.0*
                :v18.0.0 *other-id-start-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define other-id-start-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Other_ID_Start') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code points that have @('ID_Start')
     although their @('General_Category') is not that of a letter:
     they are kept so that a code point
     that could start an identifier in an earlier version
     still can [UAX #31, Section 2.5]."))
  (code-point-in-ranges-p cp (other-id-start-ranges ver))
  :hooks (:fix)

  ///

  (defruled other-id-start-p-alt-def
    (equal (other-id-start-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (and (<= #x1885 cp) ; MONGOLIAN LETTER ALI GALI BALUDA
                      (<= cp #x1886)) ; ... THREE BALUDA
                 (equal cp #x2118) ; SCRIPT CAPITAL P
                 (equal cp #x212E) ; ESTIMATED SYMBOL
                 (and (<= #x309B cp) ; KATAKANA-HIRAGANA VOICED SOUND MARK
                      (<= cp #x309C))))) ; ... SEMI-VOICED SOUND MARK
    :enable (other-id-start-ranges
             code-point-in-range-p))

  (defrule other-id-start-p-same-in-all-versions
    (equal (other-id-start-p cp ver1)
           (other-id-start-p cp ver2))
    :rule-classes nil
    :enable other-id-start-p-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define other-id-continue-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Other_ID_Continue') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *other-id-continue-v16.0.0*
                :v17.0.0 *other-id-continue-v17.0.0*
                :v18.0.0 *other-id-continue-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define other-id-continue-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Other_ID_Continue') property,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code points that have @('ID_Continue')
     although their @('General_Category')
     is not one of those that the property is derived from
     [UAX #31, Section 2.5]."))
  (code-point-in-ranges-p cp (other-id-continue-ranges ver))
  :hooks (:fix)

  ///

  (defruled other-id-continue-p-alt-def
    (equal (other-id-continue-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (or (equal cp #x00B7) ; MIDDLE DOT
                 (equal cp #x0387) ; GREEK ANO TELEIA
                 (and (<= #x1369 cp) ; ETHIOPIC DIGIT ONE
                      (<= cp #x1371)) ; ETHIOPIC DIGIT NINE
                 (equal cp #x19DA) ; NEW TAI LUE THAM DIGIT ONE
                 (equal cp #x200C) ; ZERO WIDTH NON-JOINER
                 (equal cp #x200D) ; ZERO WIDTH JOINER
                 (equal cp #x30FB) ; KATAKANA MIDDLE DOT
                 (equal cp #xFF65)))) ; HALFWIDTH KATAKANA MIDDLE DOT
    :enable (other-id-continue-ranges
             code-point-in-range-p))

  (defrule other-id-continue-p-same-in-all-versions
    (equal (other-id-continue-p cp ver1)
           (other-id-continue-p cp ver2))
    :rule-classes nil
    :enable other-id-continue-p-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection id-theorems
  :short "Theorems about @('ID_Start') and @('ID_Continue')
          that hold in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point that can start an identifier can continue one.
     A code point that has @('Other_ID_Start') has @('ID_Start'),
     and one that has @('Other_ID_Continue') has @('ID_Continue').
     No surrogate has either property.
     These are proved by evaluation on the tables, for each version:
     so adding a version checks them for that version."))

  (defrulel id-start-ranges-within-id-continue-ranges
    (ranges-within-ranges-p (id-start-ranges ver)
                            (id-continue-ranges ver))
    :enable (id-start-ranges id-continue-ranges))

  (defrulel id-continue-ranges-within-scalar-value-ranges
    (ranges-within-ranges-p (id-continue-ranges ver)
                            (scalar-value-ranges))
    :enable (id-continue-ranges (:e scalar-value-ranges)))

  (defrulel other-id-start-ranges-within-id-start-ranges
    (ranges-within-ranges-p (other-id-start-ranges ver)
                            (id-start-ranges ver))
    :enable (other-id-start-ranges id-start-ranges))

  (defrulel other-id-continue-ranges-within-id-continue-ranges
    (ranges-within-ranges-p (other-id-continue-ranges ver)
                            (id-continue-ranges ver))
    :enable (other-id-continue-ranges id-continue-ranges))

  (defrule id-continue-p-when-id-start-p
    (implies (id-start-p cp ver)
             (id-continue-p cp ver))
    :enable (id-start-p
             id-continue-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule scalar-value-p-when-id-continue-p
    (implies (and (id-continue-p cp ver)
                  (code-point-p cp))
             (scalar-value-p cp))
    :rule-classes (:rewrite :forward-chaining)
    :enable (id-continue-p
             scalar-value-p-when-code-point-in-scalar-value-ranges
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule id-start-p-when-other-id-start-p
    (implies (other-id-start-p cp ver)
             (id-start-p cp ver))
    :enable (other-id-start-p
             id-start-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule id-continue-p-when-other-id-continue-p
    (implies (other-id-continue-p cp ver)
             (id-continue-p cp ver))
    :enable (other-id-continue-p
             id-continue-p
             code-point-in-ranges-p-when-ranges-within-ranges-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection id-and-xid
  :short "The code points that have @('ID_Start') or @('ID_Continue')
          are those that have @('XID_Start') or @('XID_Continue'),
          and a few more, which we list."
  :long
  (xdoc::topstring
   (xdoc::p
    "[UAX #31, Section 5.1] derives the @('XID') properties
     from the @('ID') properties by removing code points,
     so that the four normalization forms take identifiers to identifiers
     (see @(see identifier-closure)).
     In the supported versions it removes 23 code points
     from @('ID_Start') and 19 of those from @('ID_Continue'):")
   (xdoc::ul
    (xdoc::li
     "U+037A GREEK YPOGEGRAMMENI,
      whose compatibility decomposition starts with a space.")
    (xdoc::li
     "U+0E33 THAI CHARACTER SARA AM and U+0EB3 LAO VOWEL SIGN AM,
      whose compatibility decompositions start with a mark.
      They keep @('XID_Continue').")
    (xdoc::li
     "U+309B and U+309C,
      the KATAKANA-HIRAGANA VOICED and SEMI-VOICED SOUND MARKs,
      whose compatibility decompositions start with a space.")
    (xdoc::li
     "Twenty Arabic presentation forms:
      U+FC5E to U+FC63, U+FDFA, U+FDFB,
      and the eight isolated forms of marks
      at the even code points from U+FE70 to U+FE7E.")
    (xdoc::li
     "U+FF9E and U+FF9F,
      the HALFWIDTH KATAKANA VOICED and SEMI-VOICED SOUND MARKs,
      whose compatibility decompositions are marks.
      They keep @('XID_Continue')."))
   (xdoc::p
    "The two lists are the same in every supported version.
     The theorems are proved by evaluation on the tables,
     for each version, with the @(see range-operations):
     the ranges of an @('ID') property
     are the union of the ranges of the @('XID') property
     and of the ranges of the list.
     So adding a version checks the lists for that version."))

  (define id-start-not-xid-start-ranges ()
    :returns (ranges range-listp)
    :short "The ranges of the code points
            that have @('ID_Start') and not @('XID_Start')."
    (list (range #x037A #x037A)
          (range #x0E33 #x0E33)
          (range #x0EB3 #x0EB3)
          (range #x309B #x309C)
          (range #xFC5E #xFC63)
          (range #xFDFA #xFDFB)
          (range #xFE70 #xFE70)
          (range #xFE72 #xFE72)
          (range #xFE74 #xFE74)
          (range #xFE76 #xFE76)
          (range #xFE78 #xFE78)
          (range #xFE7A #xFE7A)
          (range #xFE7C #xFE7C)
          (range #xFE7E #xFE7E)
          (range #xFF9E #xFF9F)))

  (define id-continue-not-xid-continue-ranges ()
    :returns (ranges range-listp)
    :short "The ranges of the code points
            that have @('ID_Continue') and not @('XID_Continue')."
    (list (range #x037A #x037A)
          (range #x309B #x309C)
          (range #xFC5E #xFC63)
          (range #xFDFA #xFDFB)
          (range #xFE70 #xFE70)
          (range #xFE72 #xFE72)
          (range #xFE74 #xFE74)
          (range #xFE76 #xFE76)
          (range #xFE78 #xFE78)
          (range #xFE7A #xFE7A)
          (range #xFE7C #xFE7C)
          (range #xFE7E #xFE7E)))

  (defrulel id-start-ranges-as-union
    (equal (ranges-normalize (id-start-ranges ver))
           (ranges-union (xid-start-ranges ver)
                         (id-start-not-xid-start-ranges)))
    :enable (id-start-ranges xid-start-ranges))

  (defrulel id-continue-ranges-as-union
    (equal (ranges-normalize (id-continue-ranges ver))
           (ranges-union (xid-continue-ranges ver)
                         (id-continue-not-xid-continue-ranges)))
    :enable (id-continue-ranges xid-continue-ranges))

  (defrulel xid-start-ranges-disjoint-from-the-others
    (ranges-disjoint-from-ranges-p (id-start-not-xid-start-ranges)
                                   (xid-start-ranges ver))
    :enable xid-start-ranges)

  (defrulel xid-continue-ranges-disjoint-from-the-others
    (ranges-disjoint-from-ranges-p (id-continue-not-xid-continue-ranges)
                                   (xid-continue-ranges ver))
    :enable xid-continue-ranges)

  (defruled id-start-p-in-terms-of-xid-start-p
    (equal (id-start-p cp ver)
           (or (xid-start-p cp ver)
               (code-point-in-ranges-p cp (id-start-not-xid-start-ranges))))
    :enable (id-start-p xid-start-p)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e id-start-not-xid-start-ranges))
    :use (:instance code-point-in-ranges-p-of-ranges-normalize
                    (ranges (id-start-ranges ver))))

  (defruled id-continue-p-in-terms-of-xid-continue-p
    (equal (id-continue-p cp ver)
           (or (xid-continue-p cp ver)
               (code-point-in-ranges-p
                cp (id-continue-not-xid-continue-ranges))))
    :enable (id-continue-p xid-continue-p)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e id-continue-not-xid-continue-ranges))
    :use (:instance code-point-in-ranges-p-of-ranges-normalize
                    (ranges (id-continue-ranges ver))))

  (defrule id-start-p-when-xid-start-p
    (implies (xid-start-p cp ver)
             (id-start-p cp ver))
    :enable id-start-p-in-terms-of-xid-start-p)

  (defrule id-continue-p-when-xid-continue-p
    (implies (xid-continue-p cp ver)
             (id-continue-p cp ver))
    :enable id-continue-p-in-terms-of-xid-continue-p)

  (defrule not-xid-start-p-when-in-id-start-not-xid-start-ranges
    (implies (code-point-in-ranges-p cp (id-start-not-xid-start-ranges))
             (not (xid-start-p cp ver)))
    :enable (xid-start-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p)
    :disable ((:e id-start-not-xid-start-ranges)))

  (defrule not-xid-continue-p-when-in-id-continue-not-xid-continue-ranges
    (implies (code-point-in-ranges-p
              cp (id-continue-not-xid-continue-ranges))
             (not (xid-continue-p cp ver)))
    :enable (xid-continue-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p)
    :disable ((:e id-continue-not-xid-continue-ranges))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection id-across-versions
  :short "A code point that has @('ID_Start') or @('ID_Continue')
          in a version of Unicode has it in every later version."
  :long
  (xdoc::topstring
   (xdoc::p
    "The Unicode Standard promises this
     [Stability, Property Value Stability],
     as it does for the @('XID') properties
     (see @(see xid-across-versions)).
     Here it is a theorem about the supported versions,
     in the order of @(tsee version<=),
     proved by evaluation on the tables, for each pair of versions.")
   (xdoc::p
    "The two rules are disabled by default:
     they have a version in their hypotheses
     that is not in their conclusions."))

  (defrulel id-start-ranges-within-ranges-of-later-version
    (implies (version<= ver1 ver2)
             (ranges-within-ranges-p (id-start-ranges ver1)
                                     (id-start-ranges ver2)))
    :rule-classes :forward-chaining
    :enable (version<=
             version-rank
             id-start-ranges))

  (defrulel id-continue-ranges-within-ranges-of-later-version
    (implies (version<= ver1 ver2)
             (ranges-within-ranges-p (id-continue-ranges ver1)
                                     (id-continue-ranges ver2)))
    :rule-classes :forward-chaining
    :enable (version<=
             version-rank
             id-continue-ranges))

  (defruled id-start-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (id-start-p cp ver1))
             (id-start-p cp ver2))
    :enable (id-start-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defruled id-continue-p-of-later-version
    (implies (and (version<= ver1 ver2)
                  (id-continue-p cp ver1))
             (id-continue-p cp ver2))
    :enable (id-continue-p
             code-point-in-ranges-p-when-ranges-within-ranges-p)))
