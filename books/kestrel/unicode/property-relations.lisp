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
(include-book "default-ignorable")
(include-book "variation-selectors")
(include-book "join-controls")
(include-book "noncharacters")
(include-book "prepended-concatenation-marks")
(include-book "pattern-syntax")
(include-book "pattern-white-space")
(include-book "white-space")
(include-book "bidi-controls")
(include-book "xid")
(include-book "combining-classes")
(include-book "id")
(include-book "scripts")
(include-book "bidi-class")
(include-book "decimal-digits")
(include-book "identifier-status")
(include-book "deprecated")
(include-book "quick-check")
(include-book "range-operations")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ property-relations
  :parents (unicode)
  :short "Theorems that relate properties of code points to each other,
          in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each property of this library is in a book of its own,
     which does not load the tables of the other properties.
     This book loads several of them
     and proves how they relate.")
   (xdoc::p
    "About the @('General_Category') property
     (see @(see general-category-property)),
     whose values are abbreviated by two letters:")
   (xdoc::ul
    (xdoc::li
     "A code point that is not a starter,
      that is, whose @('Canonical_Combining_Class') is not 0,
      is a combining mark:
      its value is @('Nonspacing_Mark') (@('Mn')),
      @('Spacing_Mark') (@('Mc')) or @('Enclosing_Mark') (@('Me')).")
    (xdoc::li
     "Every variation selector is a @('Nonspacing_Mark') (@('Mn')).")
    (xdoc::li
     "Every bidirectional control, every join control
      and every prepended concatenation mark
      is a @('Format') character (@('Cf')).")
    (xdoc::li
     "Every noncharacter is @('Unassigned') (@('Cn')),
      so it is not assigned in the sense of @(tsee assigned-p)."))
   (xdoc::p
    "About the @('Default_Ignorable_Code_Point') property
     (see @(see default-ignorable)):")
   (xdoc::ul
    (xdoc::li
     "Every variation selector, every bidirectional control
      and every join control has it.")
    (xdoc::li
     "No prepended concatenation mark has it:
      these are the format characters that are visible."))
   (xdoc::p
    "About the @('Pattern_Syntax') property
     (see @(see pattern-syntax)):")
   (xdoc::ul
    (xdoc::li
     "No code point has both @('Pattern_Syntax')
      and @('Pattern_White_Space').")
    (xdoc::li
     "No code point has both @('Pattern_Syntax')
      and @('XID_Continue'), or @('XID_Start'):
      a character of syntax is never a character of an identifier."))
   (xdoc::p
    "About the @('White_Space') property (see @(see white-space)):")
   (xdoc::ul
    (xdoc::li
     "A code point that has @('Pattern_White_Space')
      has @('White_Space'),
      unless it is one of the two directional marks.")
    (xdoc::li
     "The code points that have @('White_Space')
      are those whose @('General_Category') is
      @('Space_Separator') (@('Zs')), @('Line_Separator') (@('Zl'))
      or @('Paragraph_Separator') (@('Zp')),
      and six control characters.
      See @(see white-space-relations)."))
   (xdoc::p
    "About @('ID_Start') and @('ID_Continue') (see @(see id-properties)):")
   (xdoc::ul
    (xdoc::li
     "They are what [UAX #31] derives them from:
      the letters and the letter numbers, and for @('ID_Continue')
      also the marks, the decimal digits and the connector punctuation,
      with the code points of @('Other_ID_Start')
      and @('Other_ID_Continue'),
      and without those of @('Pattern_Syntax')
      and @('Pattern_White_Space').
      See @(see id-relations)."))
   (xdoc::p
    "About the scripts, the bidirectional classes and the decimal digits:")
   (xdoc::ul
    (xdoc::li
     "The code points whose @('Script') is @('Unknown')
      are those whose @('General_Category') is
      @('Unassigned') (@('Cn')), @('Private_Use') (@('Co'))
      or @('Surrogate') (@('Cs')).")
    (xdoc::li
     "A code point whose @('Bidi_Class') is @('Nonspacing_Mark')
      is a @('Nonspacing_Mark') (@('Mn'))
      or an @('Enclosing_Mark') (@('Me')).")
    (xdoc::li
     "The decimal digits are the code points
      whose @('General_Category') is @('Decimal_Number') (@('Nd'))."))
   (xdoc::p
    "About the @('Identifier_Type') property of [UTS #39]
     (see @(see identifier-status)),
     whose types are defined in terms of other properties:
     see @(see identifier-type-relations).")
   (xdoc::p
    "These are proved by evaluation on the tables, for each version:
     so adding a version checks them for that version,
     and if one fails, that is a change in Unicode to look at.
     Most are proved on lists of ranges,
     with the @(see range-operations):
     that the code points of one property are among those of another
     is the fact that a difference of two lists of ranges is empty."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection general-category-relations
  :short "Theorems that relate @('General_Category') to other properties."

  ;; We prove the first theorem
  ;; by checking it on every code point, for each version.

  (local
   (define mark-ok ((cp code-point-p)
                    (map combining-class-mapp)
                    (runs general-category-run-listp))
     :returns (yes/no booleanp)
     (or (equal (combining-class-map-lookup cp map) 0)
         (general-category-mark-p
          (general-category-run-list-lookup cp runs)))
     :hooks nil))

  (local
   (std::deflist mark-ok-listp (x map runs)
     :guard (and (code-point-listp x)
                 (combining-class-mapp map)
                 (general-category-run-listp runs))
     (mark-ok x map runs)))

  (defrulel mark-ok-listp-of-all-code-points
    (mark-ok-listp (all-code-points)
                   (canonical-combining-class-map ver)
                   (general-category-runs ver))
    :enable (canonical-combining-class-map
             general-category-runs
             (:e all-code-points))
    :disable mark-ok-listp-of-cons)

  (defrule general-category-mark-p-when-not-starter-p
    (implies (not (starter-p cp ver))
             (general-category-mark-p (code-point-general-category cp ver)))
    :enable (mark-ok
             starter-p
             canonical-combining-class
             code-point-general-category)
    :use (:instance mark-ok-when-member-equal-of-mark-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (map (canonical-combining-class-map ver))
                    (runs (general-category-runs ver))))

  ;; The other theorems say that the code points of a property
  ;; all have a certain General_Category.
  ;; Each is proved by evaluating, on the tables,
  ;; that the ranges of the property
  ;; are within the ranges of that General_Category.

  (defrulel variation-selector-ranges-within-nonspacing-mark-ranges
    (ranges-within-ranges-p
     (variation-selector-ranges ver)
     (general-category-ranges (general-category-nonspacing-mark) ver))
    :enable (variation-selector-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-variation-selector-p
    (implies (variation-selector-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-nonspacing-mark)))
    :enable (variation-selector-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-nonspacing-mark)))

  (defrulel bidi-control-ranges-within-format-ranges
    (ranges-within-ranges-p
     (bidi-control-ranges ver)
     (general-category-ranges (general-category-format) ver))
    :enable (bidi-control-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-bidi-control-p
    (implies (bidi-control-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-format)))
    :enable (bidi-control-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-format)))

  (defrulel join-control-ranges-within-format-ranges
    (ranges-within-ranges-p
     (join-control-ranges ver)
     (general-category-ranges (general-category-format) ver))
    :enable (join-control-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-join-control-p
    (implies (join-control-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-format)))
    :enable (join-control-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-format)))

  (defrulel prepended-concatenation-mark-ranges-within-format-ranges
    (ranges-within-ranges-p
     (prepended-concatenation-mark-ranges ver)
     (general-category-ranges (general-category-format) ver))
    :enable (prepended-concatenation-mark-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-prepended-concatenation-mark-p
    (implies (prepended-concatenation-mark-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-format)))
    :enable (prepended-concatenation-mark-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-format)))

  (defrulel noncharacter-ranges-within-unassigned-ranges
    (ranges-within-ranges-p
     (noncharacter-ranges ver)
     (general-category-ranges (general-category-unassigned) ver))
    :enable (noncharacter-ranges
             general-category-ranges
             general-category-runs))

  (defruled code-point-general-category-when-noncharacter-p
    (implies (noncharacter-p cp ver)
             (equal (code-point-general-category cp ver)
                    (general-category-unassigned)))
    :enable (noncharacter-p
             equal-of-code-point-general-category
             code-point-in-ranges-p-when-ranges-within-ranges-p)
    :disable ((:e general-category-unassigned)))

  (defrule not-assigned-p-when-noncharacter-p
    (implies (noncharacter-p cp ver)
             (not (assigned-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (assigned-p
             code-point-general-category-when-noncharacter-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection default-ignorable-relations
  :short "Theorems that relate @('Default_Ignorable_Code_Point')
          to other properties."

  (defrulel variation-selector-ranges-within-default-ignorable-ranges
    (ranges-within-ranges-p (variation-selector-ranges ver)
                            (default-ignorable-ranges ver))
    :enable (variation-selector-ranges
             default-ignorable-ranges))

  (defrule default-ignorable-p-when-variation-selector-p
    (implies (variation-selector-p cp ver)
             (default-ignorable-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (variation-selector-p
             default-ignorable-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel bidi-control-ranges-within-default-ignorable-ranges
    (ranges-within-ranges-p (bidi-control-ranges ver)
                            (default-ignorable-ranges ver))
    :enable (bidi-control-ranges
             default-ignorable-ranges))

  (defrule default-ignorable-p-when-bidi-control-p
    (implies (bidi-control-p cp ver)
             (default-ignorable-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (bidi-control-p
             default-ignorable-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel join-control-ranges-within-default-ignorable-ranges
    (ranges-within-ranges-p (join-control-ranges ver)
                            (default-ignorable-ranges ver))
    :enable (join-control-ranges
             default-ignorable-ranges))

  (defrule default-ignorable-p-when-join-control-p
    (implies (join-control-p cp ver)
             (default-ignorable-p cp ver))
    :rule-classes (:rewrite :forward-chaining)
    :enable (join-control-p
             default-ignorable-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel prepended-concatenation-mark-ranges-disjoint-from-default-ignorable
    (ranges-disjoint-from-ranges-p (prepended-concatenation-mark-ranges ver)
                                   (default-ignorable-ranges ver))
    :enable (prepended-concatenation-mark-ranges
             default-ignorable-ranges))

  (defrule not-default-ignorable-p-when-prepended-concatenation-mark-p
    (implies (prepended-concatenation-mark-p cp ver)
             (not (default-ignorable-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (prepended-concatenation-mark-p
             default-ignorable-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pattern-syntax-relations
  :short "Theorems that relate @('Pattern_Syntax')
          and @('Pattern_White_Space') to other properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point that has @('Pattern_Syntax') or @('Pattern_White_Space')
     does not have @('XID_Continue'), and so not @('XID_Start') either:
     the characters of syntax and of white space
     are not characters of identifiers.
     The Unicode Standard promises
     that this will stay so [Stability, Property Value Stability].
     No code point has both @('Pattern_Syntax')
     and @('Pattern_White_Space')."))

  (defrulel pattern-syntax-ranges-disjoint-from-pattern-white-space-ranges
    (ranges-disjoint-from-ranges-p (pattern-syntax-ranges ver)
                                   (pattern-white-space-ranges ver))
    :enable (pattern-syntax-ranges
             pattern-white-space-ranges))

  (defrule not-pattern-white-space-p-when-pattern-syntax-p
    (implies (pattern-syntax-p cp ver)
             (not (pattern-white-space-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (pattern-syntax-p
             pattern-white-space-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p))

  (defrulel pattern-syntax-ranges-disjoint-from-xid-continue-ranges
    (ranges-disjoint-from-ranges-p (pattern-syntax-ranges ver)
                                   (xid-continue-ranges ver))
    :enable (pattern-syntax-ranges
             xid-continue-ranges))

  (defrule not-xid-continue-p-when-pattern-syntax-p
    (implies (pattern-syntax-p cp ver)
             (not (xid-continue-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (pattern-syntax-p
             xid-continue-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p))

  (defrule not-xid-start-p-when-pattern-syntax-p
    (implies (pattern-syntax-p cp ver)
             (not (xid-start-p cp ver)))
    :rule-classes (:rewrite :forward-chaining))

  (defrulel pattern-white-space-ranges-disjoint-from-xid-continue-ranges
    (ranges-disjoint-from-ranges-p (pattern-white-space-ranges ver)
                                   (xid-continue-ranges ver))
    :enable (pattern-white-space-ranges
             xid-continue-ranges))

  (defrule not-xid-continue-p-when-pattern-white-space-p
    (implies (pattern-white-space-p cp ver)
             (not (xid-continue-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)
    :enable (pattern-white-space-p
             xid-continue-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p))

  (defrule not-xid-start-p-when-pattern-white-space-p
    (implies (pattern-white-space-p cp ver)
             (not (xid-start-p cp ver)))
    :rule-classes (:rewrite :forward-chaining)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection white-space-relations
  :short "Theorems that relate @('White_Space')
          to @('Pattern_White_Space') and to @('General_Category')."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point that has @('Pattern_White_Space')
     has @('White_Space') too,
     unless it is U+200E LEFT-TO-RIGHT MARK or U+200F RIGHT-TO-LEFT MARK,
     which are format characters and not spaces.")
   (xdoc::p
    "The code points that have @('White_Space') are the separators,
     that is, those whose @('General_Category') is
     @('Space_Separator') (@('Zs')), @('Line_Separator') (@('Zl'))
     or @('Paragraph_Separator') (@('Zp')),
     and six control characters:
     the five from U+0009 to U+000D, and U+0085.
     The second theorem is proved by evaluating, on the tables,
     that the two lists of ranges cover the same code points."))

  (defrule white-space-p-when-pattern-white-space-p
    (implies (and (pattern-white-space-p cp ver)
                  (not (equal (code-point-fix cp) #x200E))
                  (not (equal (code-point-fix cp) #x200F)))
             (white-space-p cp ver))
    :enable (pattern-white-space-p-alt-def
             white-space-p-alt-def)
    :disable (pattern-white-space-p white-space-p))

  (defrulel white-space-ranges-as-general-categories
    (equal (ranges-normalize (white-space-ranges ver))
           (ranges-normalize
            (append
             (general-category-ranges (general-category-space-separator)
                                      ver)
             (general-category-ranges (general-category-line-separator)
                                      ver)
             (general-category-ranges (general-category-paragraph-separator)
                                      ver)
             (list (range #x0009 #x000D)
                   (range #x0085 #x0085)))))
    :enable (white-space-ranges
             general-category-ranges
             general-category-runs))

  (defruled white-space-p-in-terms-of-general-category
    (equal (white-space-p cp ver)
           (b* ((gc (code-point-general-category cp ver))
                (cp (code-point-fix cp)))
             (or (general-category-separator-p gc)
                 (and (<= #x0009 cp)
                      (<= cp #x000D))
                 (equal cp #x0085))))
    :enable (white-space-p
             general-category-separator-p
             code-point-in-general-category-ranges
             equal-of-general-category-space-separator
             equal-of-general-category-line-separator
             equal-of-general-category-paragraph-separator
             code-point-in-range-p)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e general-category-space-separator)
              (:e general-category-line-separator)
              (:e general-category-paragraph-separator))
    :use ((:instance code-point-in-ranges-p-of-ranges-normalize
                     (ranges (white-space-ranges ver)))
          (:instance
           code-point-in-ranges-p-of-ranges-normalize
           (ranges
            (append
             (general-category-ranges (general-category-space-separator)
                                      ver)
             (general-category-ranges (general-category-line-separator)
                                      ver)
             (general-category-ranges (general-category-paragraph-separator)
                                      ver)
             (list (range #x0009 #x000D)
                   (range #x0085 #x0085))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection id-relations
  :short "@('ID_Start') and @('ID_Continue')
          are derived from the @('General_Category')
          as [UAX #31] says."
  :long
  (xdoc::topstring
   (xdoc::p
    "In these names, @('ID') is short for `identifier'.
     [UAX #31, Table 2] defines the two properties as follows.
     A code point has @('ID_Start')
     if its @('General_Category') is that of a letter
     or is @('Letter_Number') (abbreviated @('Nl')),
     or it has @('Other_ID_Start');
     unless it has @('Pattern_Syntax') or @('Pattern_White_Space').
     A code point has @('ID_Continue')
     if it has @('ID_Start'),
     or its @('General_Category') is
     @('Nonspacing_Mark') (@('Mn')), @('Spacing_Mark') (@('Mc')),
     @('Decimal_Number') (@('Nd'))
     or @('Connector_Punctuation') (@('Pc')),
     or it has @('Other_ID_Continue');
     with the same exception.")
   (xdoc::p
    "The library takes the two properties from the file
     @('DerivedCoreProperties.txt') and does not recompute them.
     The theorems here say that the file agrees with the definition,
     for each supported version.
     They are proved with the @(see range-operations):
     the ranges of each property, in normal form,
     are equal to the ranges that the definition gives,
     which are computed from the tables of the other properties."))

  (defrulel id-start-ranges-as-derived
    (equal (ranges-normalize (id-start-ranges ver))
           (ranges-difference
            (ranges-difference
             (append
              (general-category-ranges (general-category-uppercase-letter)
                                       ver)
              (general-category-ranges (general-category-lowercase-letter)
                                       ver)
              (general-category-ranges (general-category-titlecase-letter)
                                       ver)
              (general-category-ranges (general-category-modifier-letter)
                                       ver)
              (general-category-ranges (general-category-other-letter) ver)
              (general-category-ranges (general-category-letter-number) ver)
              (other-id-start-ranges ver))
             (pattern-syntax-ranges ver))
            (pattern-white-space-ranges ver)))
    :enable (id-start-ranges
             general-category-ranges
             general-category-runs
             other-id-start-ranges
             pattern-syntax-ranges
             pattern-white-space-ranges))

  (defrulel id-continue-ranges-as-derived
    (equal (ranges-normalize (id-continue-ranges ver))
           (ranges-difference
            (ranges-difference
             (append
              (id-start-ranges ver)
              (general-category-ranges (general-category-nonspacing-mark)
                                       ver)
              (general-category-ranges (general-category-spacing-mark) ver)
              (general-category-ranges (general-category-decimal-number)
                                       ver)
              (general-category-ranges
               (general-category-connector-punctuation) ver)
              (other-id-continue-ranges ver))
             (pattern-syntax-ranges ver))
            (pattern-white-space-ranges ver)))
    :enable (id-continue-ranges
             id-start-ranges
             general-category-ranges
             general-category-runs
             other-id-continue-ranges
             pattern-syntax-ranges
             pattern-white-space-ranges))

  (defruled id-start-p-in-terms-of-general-category
    (equal (id-start-p cp ver)
           (b* ((gc (code-point-general-category cp ver)))
             (and (or (general-category-letter-p gc)
                      (general-category-case gc :letter-number)
                      (other-id-start-p cp ver))
                  (not (pattern-syntax-p cp ver))
                  (not (pattern-white-space-p cp ver)))))
    :enable (id-start-p
             other-id-start-p
             pattern-syntax-p
             pattern-white-space-p
             general-category-letter-p
             code-point-in-general-category-ranges
             equal-of-general-category-uppercase-letter
             equal-of-general-category-lowercase-letter
             equal-of-general-category-titlecase-letter
             equal-of-general-category-modifier-letter
             equal-of-general-category-other-letter
             equal-of-general-category-letter-number)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e general-category-uppercase-letter)
              (:e general-category-lowercase-letter)
              (:e general-category-titlecase-letter)
              (:e general-category-modifier-letter)
              (:e general-category-other-letter)
              (:e general-category-letter-number))
    :use (:instance code-point-in-ranges-p-of-ranges-normalize
                    (ranges (id-start-ranges ver))))

  (defruled id-continue-p-in-terms-of-general-category
    (equal (id-continue-p cp ver)
           (b* ((gc (code-point-general-category cp ver)))
             (and (or (id-start-p cp ver)
                      (general-category-case gc :nonspacing-mark)
                      (general-category-case gc :spacing-mark)
                      (general-category-case gc :decimal-number)
                      (general-category-case gc :connector-punctuation)
                      (other-id-continue-p cp ver))
                  (not (pattern-syntax-p cp ver))
                  (not (pattern-white-space-p cp ver)))))
    :enable (id-continue-p
             id-start-p
             other-id-continue-p
             pattern-syntax-p
             pattern-white-space-p
             code-point-in-general-category-ranges
             equal-of-general-category-nonspacing-mark
             equal-of-general-category-spacing-mark
             equal-of-general-category-decimal-number
             equal-of-general-category-connector-punctuation)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e general-category-nonspacing-mark)
              (:e general-category-spacing-mark)
              (:e general-category-decimal-number)
              (:e general-category-connector-punctuation))
    :use (:instance code-point-in-ranges-p-of-ranges-normalize
                    (ranges (id-continue-ranges ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection script-relations
  :short "The code points whose @('Script') is @('Unknown')
          are the unassigned code points, the private-use code points
          and the surrogates."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, those whose @('General_Category') is
     @('Unassigned'), @('Private_Use') or @('Surrogate')
     (abbreviated @('Cn'), @('Co') and @('Cs')).
     So every assigned character, other than those of private use,
     has a script, which can be @('Common') or @('Inherited')."))

  (defrulel unknown-script-ranges-as-general-categories
    (equal (ranges-normalize (script-ranges (script-unknown) ver))
           (ranges-normalize
            (append
             (general-category-ranges (general-category-unassigned) ver)
             (general-category-ranges (general-category-private-use) ver)
             (general-category-ranges (general-category-surrogate) ver))))
    :enable (script-ranges
             script-runs
             general-category-ranges
             general-category-runs))

  (defruled script-unknown-in-terms-of-general-category
    (equal (equal (code-point-script cp ver) (script-unknown))
           (b* ((gc (code-point-general-category cp ver)))
             (or (general-category-case gc :unassigned)
                 (general-category-case gc :private-use)
                 (general-category-case gc :surrogate))))
    :enable (equal-of-code-point-script
             code-point-in-general-category-ranges
             equal-of-general-category-unassigned
             equal-of-general-category-private-use
             equal-of-general-category-surrogate)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e script-unknown)
              (:e general-category-unassigned)
              (:e general-category-private-use)
              (:e general-category-surrogate))
    :use ((:instance code-point-in-ranges-p-of-ranges-normalize
                     (ranges (script-ranges (script-unknown) ver)))
          (:instance
           code-point-in-ranges-p-of-ranges-normalize
           (ranges
            (append
             (general-category-ranges (general-category-unassigned) ver)
             (general-category-ranges (general-category-private-use) ver)
             (general-category-ranges (general-category-surrogate)
                                      ver)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-class-relations
  :short "A code point whose @('Bidi_Class') is @('Nonspacing_Mark')
          is a nonspacing mark or an enclosing mark."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, its @('General_Category') is
     @('Nonspacing_Mark') or @('Enclosing_Mark')
     (abbreviated @('Mn') and @('Me')).
     The converse does not hold:
     a few marks of those two categories have other bidirectional classes."))

  (defrulel nonspacing-mark-class-ranges-less-mark-ranges
    (equal (ranges-difference
            (bidi-class-ranges (bidi-class-nonspacing-mark) ver)
            (append
             (general-category-ranges (general-category-nonspacing-mark)
                                      ver)
             (general-category-ranges (general-category-enclosing-mark)
                                      ver)))
           nil)
    :enable (bidi-class-ranges
             bidi-class-runs
             general-category-ranges
             general-category-runs))

  (defruled general-category-when-bidi-class-nonspacing-mark
    (implies (equal (code-point-bidi-class cp ver)
                    (bidi-class-nonspacing-mark))
             (b* ((kind (general-category-kind
                         (code-point-general-category cp ver))))
               (or (equal kind :nonspacing-mark)
                   (equal kind :enclosing-mark))))
    :enable (equal-of-code-point-bidi-class
             code-point-in-general-category-ranges
             equal-of-general-category-nonspacing-mark
             equal-of-general-category-enclosing-mark)
    :disable ((:e bidi-class-nonspacing-mark)
              (:e general-category-nonspacing-mark)
              (:e general-category-enclosing-mark))
    :use (:instance
          code-point-in-ranges-p-when-ranges-difference-is-empty
          (ranges1 (bidi-class-ranges (bidi-class-nonspacing-mark) ver))
          (ranges2
           (append
            (general-category-ranges (general-category-nonspacing-mark)
                                     ver)
            (general-category-ranges (general-category-enclosing-mark)
                                     ver))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection decimal-digit-relations
  :short "The decimal digits are the code points
          whose @('General_Category') is @('Decimal_Number')."
  :long
  (xdoc::topstring
   (xdoc::p
    "That value is abbreviated @('Nd').
     The decimal digits come from field 6 of the file
     @('UnicodeData.txt') (see @(see decimal-digits)),
     and the @('General_Category') from another file.
     We check one direction on every code point
     and the other on the code points of the ranges of the category,
     for each version."))

  (local
   (define digit-is-nd ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (not (decimal-digit-value cp ver))
         (code-point-in-ranges-p
          cp
          (general-category-ranges (general-category-decimal-number) ver)))
     :hooks nil))

  (local
   (std::deflist digit-is-nd-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (digit-is-nd x ver)))

  (defrulel digit-is-nd-listp-of-all-code-points
    (digit-is-nd-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable digit-is-nd-listp-of-cons)

  (local
   (std::deflist decimal-digit-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (decimal-digit-p x ver)))

  (defrulel decimal-digit-listp-of-decimal-number-code-points
    (decimal-digit-listp
     (range-list-code-points
      (general-category-ranges (general-category-decimal-number)
                               (version-fix ver)))
     (version-fix ver))
    :rule-classes nil
    :enable version-fix-in-terms-of-version-case
    :disable decimal-digit-listp-of-cons)

  (defruled decimal-digit-p-in-terms-of-general-category
    (equal (decimal-digit-p cp ver)
           (general-category-case (code-point-general-category cp ver)
                                  :decimal-number))
    :enable (decimal-digit-p
             digit-is-nd
             code-point-in-general-category-ranges
             equal-of-general-category-decimal-number)
    :disable ((:e general-category-decimal-number)
              digit-is-nd-when-member-equal-of-digit-is-nd-listp
              decimal-digit-p-when-member-equal-of-decimal-digit-listp)
    :use (decimal-digit-listp-of-decimal-number-code-points
          (:instance digit-is-nd-when-member-equal-of-digit-is-nd-listp
                     (acl2::a (code-point-fix cp))
                     (x (all-code-points))
                     (ver (version-fix ver)))
          (:instance
           decimal-digit-p-when-member-equal-of-decimal-digit-listp
           (acl2::a (code-point-fix cp))
           (x (range-list-code-points
               (general-category-ranges (general-category-decimal-number)
                                        (version-fix ver))))
           (ver (version-fix ver))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection identifier-type-relations
  :short "Theorems that relate the @('Identifier_Type') property
          and the @('Identifier_Status') property to other properties."
  :long
  (xdoc::topstring
   (xdoc::p
    "[UTS #39, Table 1] describes several of the identifier types
     in terms of other properties.
     In the supported versions of Unicode
     the data agree with those descriptions as follows.")
   (xdoc::ul
    (xdoc::li
     "A code point has the type @('Not_Character') exactly when
      its @('General_Category') is @('Unassigned'), @('Private_Use')
      or @('Surrogate'),
      or it is @('Control') and the code point
      does not have @('Pattern_White_Space').")
    (xdoc::li
     "A code point has the type @('Deprecated')
      exactly when it has the @('Deprecated') property.")
    (xdoc::li
     "A code point that has the type @('Default_Ignorable')
      has the @('Default_Ignorable_Code_Point') property.
      The converse does not hold:
      a code point with that property that has an earlier type
      in the table, such as @('Deprecated'), gets that type.")
    (xdoc::li
     "A code point that has the type @('Not_NFKC')
      has the value `no' for the @('NFKC_Quick_Check') property,
      that is, Normalization Form KC (NFKC) changes it.
      The converse fails for seven code points,
      which are @('Deprecated') or @('Default_Ignorable').")
    (xdoc::li
     "A code point that has the type @('Not_XID')
      does not have @('XID_Continue')."))
   (xdoc::p
    "And about the status:
     no code point that is @('Allowed')
     has the value `no' for the @('NFKC_Quick_Check') property.
     The same facts, said of the normalization function,
     are in @(see identifier-status-and-normalization).")
   (xdoc::p
    "These are proved by evaluation on lists of ranges,
     for each version."))

  ;; Not_Character.

  (defrulel not-character-ranges-as-general-categories
    (equal (ranges-normalize
            (identifier-type-ranges (identifier-type-not-character) ver))
           (ranges-normalize
            (append
             (general-category-ranges (general-category-unassigned) ver)
             (general-category-ranges (general-category-private-use) ver)
             (general-category-ranges (general-category-surrogate) ver)
             (ranges-difference
              (general-category-ranges (general-category-control) ver)
              (pattern-white-space-ranges ver)))))
    :enable (identifier-type-ranges
             identifier-type-runs
             general-category-ranges
             general-category-runs
             pattern-white-space-ranges))

  (defruled identifier-type-not-character-in-terms-of-general-category
    (iff (member-equal (identifier-type-not-character)
                       (code-point-identifier-types cp ver))
         (b* ((gc (code-point-general-category cp ver)))
           (or (general-category-case gc :unassigned)
               (general-category-case gc :private-use)
               (general-category-case gc :surrogate)
               (and (general-category-case gc :control)
                    (not (pattern-white-space-p cp ver))))))
    :enable (pattern-white-space-p
             code-point-in-general-category-ranges
             equal-of-general-category-unassigned
             equal-of-general-category-private-use
             equal-of-general-category-surrogate
             equal-of-general-category-control)
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e identifier-type-not-character)
              (:e general-category-unassigned)
              (:e general-category-private-use)
              (:e general-category-surrogate)
              (:e general-category-control))
    :use ((:instance code-point-in-identifier-type-ranges
                     (type (identifier-type-not-character)))
          (:instance code-point-in-ranges-p-of-ranges-normalize
                     (ranges (identifier-type-ranges
                              (identifier-type-not-character) ver)))
          (:instance
           code-point-in-ranges-p-of-ranges-normalize
           (ranges
            (append
             (general-category-ranges (general-category-unassigned) ver)
             (general-category-ranges (general-category-private-use) ver)
             (general-category-ranges (general-category-surrogate) ver)
             (ranges-difference
              (general-category-ranges (general-category-control) ver)
              (pattern-white-space-ranges ver)))))))

  ;; Deprecated.

  (defrulel deprecated-type-ranges-are-deprecated-ranges
    (equal (ranges-normalize
            (identifier-type-ranges (identifier-type-deprecated) ver))
           (ranges-normalize (deprecated-ranges ver)))
    :enable (identifier-type-ranges
             identifier-type-runs
             deprecated-ranges))

  (defruled identifier-type-deprecated-in-terms-of-deprecated-p
    (iff (member-equal (identifier-type-deprecated)
                       (code-point-identifier-types cp ver))
         (deprecated-p cp ver))
    :enable deprecated-p
    :disable (code-point-in-ranges-p-of-ranges-normalize
              (:e identifier-type-deprecated))
    :use ((:instance code-point-in-identifier-type-ranges
                     (type (identifier-type-deprecated)))
          (:instance code-point-in-ranges-p-of-ranges-normalize
                     (ranges (identifier-type-ranges
                              (identifier-type-deprecated) ver)))
          (:instance code-point-in-ranges-p-of-ranges-normalize
                     (ranges (deprecated-ranges ver)))))

  ;; Default_Ignorable.

  (defrulel default-ignorable-type-ranges-less-default-ignorable-ranges
    (equal (ranges-difference
            (identifier-type-ranges (identifier-type-default-ignorable) ver)
            (default-ignorable-ranges ver))
           nil)
    :enable (identifier-type-ranges
             identifier-type-runs
             default-ignorable-ranges))

  (defruled default-ignorable-p-when-identifier-type-default-ignorable
    (implies (member-equal (identifier-type-default-ignorable)
                           (code-point-identifier-types cp ver))
             (default-ignorable-p cp ver))
    :enable default-ignorable-p
    :disable ((:e identifier-type-default-ignorable))
    :use ((:instance code-point-in-identifier-type-ranges
                     (type (identifier-type-default-ignorable)))
          (:instance
           code-point-in-ranges-p-when-ranges-difference-is-empty
           (ranges1 (identifier-type-ranges
                     (identifier-type-default-ignorable) ver))
           (ranges2 (default-ignorable-ranges ver)))))

  ;; Not_NFKC.

  (defrulel not-nfkc-type-ranges-less-quick-check-no-ranges
    (equal (ranges-difference
            (identifier-type-ranges (identifier-type-not-nfkc) ver)
            (nfkc-quick-check-no-ranges ver))
           nil)
    :enable (identifier-type-ranges
             identifier-type-runs
             nfkc-quick-check-no-ranges))

  (defruled nfkc-quick-check-no-when-identifier-type-not-nfkc
    (implies (member-equal (identifier-type-not-nfkc)
                           (code-point-identifier-types cp ver))
             (equal (quick-check-value-kind (nfkc-quick-check cp ver))
                    :no))
    :enable nfkc-quick-check
    :disable ((:e identifier-type-not-nfkc))
    :use ((:instance code-point-in-identifier-type-ranges
                     (type (identifier-type-not-nfkc)))
          (:instance
           code-point-in-ranges-p-when-ranges-difference-is-empty
           (ranges1 (identifier-type-ranges
                     (identifier-type-not-nfkc) ver))
           (ranges2 (nfkc-quick-check-no-ranges ver)))))

  ;; Not_XID.

  (defrulel not-xid-type-ranges-disjoint-from-xid-continue-ranges
    (ranges-disjoint-from-ranges-p
     (identifier-type-ranges (identifier-type-not-xid) ver)
     (xid-continue-ranges ver))
    :enable (identifier-type-ranges
             identifier-type-runs
             xid-continue-ranges))

  (defruled not-xid-continue-p-when-identifier-type-not-xid
    (implies (member-equal (identifier-type-not-xid)
                           (code-point-identifier-types cp ver))
             (not (xid-continue-p cp ver)))
    :enable (xid-continue-p
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p)
    :disable ((:e identifier-type-not-xid))
    :use (:instance code-point-in-identifier-type-ranges
                    (type (identifier-type-not-xid))))

  ;; Allowed.

  (defrulel identifier-allowed-ranges-disjoint-from-quick-check-no-ranges
    (ranges-disjoint-from-ranges-p (identifier-allowed-ranges ver)
                                   (nfkc-quick-check-no-ranges ver))
    :enable (identifier-allowed-ranges
             nfkc-quick-check-no-ranges))

  (defruled not-nfkc-quick-check-no-when-identifier-allowed-p
    (implies (identifier-allowed-p cp ver)
             (not (equal (quick-check-value-kind (nfkc-quick-check cp ver))
                         :no)))
    :enable (identifier-allowed-p
             nfkc-quick-check
             not-code-point-in-ranges-p-when-ranges-disjoint-from-ranges-p)))
