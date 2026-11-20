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

(include-book "data/v16.0.0/emoji-data")
(include-book "data/v17.0.0/emoji-data")
(include-book "data/v18.0.0/emoji-data")
(include-book "data/v16.0.0/prop-list")
(include-book "data/v17.0.0/prop-list")
(include-book "data/v18.0.0/prop-list")

(local (include-book "range-operations"))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ emoji
  :parents (unicode)
  :short "The emoji properties, and the @('Regional_Indicator') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode Technical Standard #51, Unicode Emoji,
     which we cite as [UTS #51],
     defines six binary properties of code points
     [UTS #51, Annex A]:")
   (xdoc::ul
    (xdoc::li
     "@('Emoji'): the characters that are emoji.
      Some of them, such as the digits, are shown as text
      unless something after them asks for an emoji.")
    (xdoc::li
     "@('Emoji_Presentation'): the emoji that are shown as emoji,
      in color, when nothing asks otherwise.")
    (xdoc::li
     "@('Emoji_Modifier'): the five skin tone modifiers.")
    (xdoc::li
     "@('Emoji_Modifier_Base'):
      the emoji that a skin tone modifier can follow.")
    (xdoc::li
     "@('Emoji_Component'): the characters that occur in emoji sequences
      and that are not meant to be shown alone as emoji,
      such as the digits, the joiner and the tag characters.")
    (xdoc::li
     "@('Extended_Pictographic'): the pictographs,
      including code points that are reserved for future emoji;
      the rules for grapheme clusters use it."))
   (xdoc::p
    "The @('Regional_Indicator') property
     is that of the twenty-six regional indicator symbols,
     pairs of which make the flags of countries.")
   (xdoc::p
    "We take the six emoji properties from the file
     @('emoji/emoji-data.txt'), and @('Regional_Indicator')
     from the file @('PropList.txt'),
     of the Unicode Character Database, for each supported version.")
   (xdoc::p
    "These properties are not stable.
     Each version adds emoji,
     and @('Extended_Pictographic') lost code points
     in Unicode 17.0.0 and in Unicode 18.0.0.
     The emoji sequences, which are made of several code points,
     are not in this library."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emoji-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points that have the @('Emoji') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *emoji-v16.0.0*
                :v17.0.0 *emoji-v17.0.0*
                :v18.0.0 *emoji-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define emoji-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Emoji') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (emoji-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emoji-presentation-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Emoji_Presentation') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *emoji-presentation-v16.0.0*
                :v17.0.0 *emoji-presentation-v17.0.0*
                :v18.0.0 *emoji-presentation-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define emoji-presentation-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Emoji_Presentation') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (emoji-presentation-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emoji-modifier-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Emoji_Modifier') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *emoji-modifier-v16.0.0*
                :v17.0.0 *emoji-modifier-v17.0.0*
                :v18.0.0 *emoji-modifier-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define emoji-modifier-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Emoji_Modifier') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (emoji-modifier-ranges ver))
  :hooks (:fix)

  ///

  (defruled emoji-modifier-p-alt-def
    (equal (emoji-modifier-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (and (<= #x1F3FB cp) ; EMOJI MODIFIER FITZPATRICK TYPE-1-2
                  (<= cp #x1F3FF)))) ; EMOJI MODIFIER FITZPATRICK TYPE-6
    :enable (emoji-modifier-ranges
             code-point-in-range-p))

  (defrule emoji-modifier-p-same-in-all-versions
    (equal (emoji-modifier-p cp ver1)
           (emoji-modifier-p cp ver2))
    :rule-classes nil
    :enable emoji-modifier-p-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emoji-modifier-base-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Emoji_Modifier_Base') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *emoji-modifier-base-v16.0.0*
                :v17.0.0 *emoji-modifier-base-v17.0.0*
                :v18.0.0 *emoji-modifier-base-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define emoji-modifier-base-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Emoji_Modifier_Base') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (emoji-modifier-base-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define emoji-component-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Emoji_Component') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *emoji-component-v16.0.0*
                :v17.0.0 *emoji-component-v17.0.0*
                :v18.0.0 *emoji-component-v18.0.0*)
  :hooks (:fix)

  ///

  (defruled emoji-component-ranges-alt-def
    (equal (emoji-component-ranges ver)
           (list (range #x0023 #x0023) ; NUMBER SIGN
                 (range #x002A #x002A) ; ASTERISK
                 (range #x0030 #x0039) ; DIGIT ZERO to DIGIT NINE
                 (range #x200D #x200D) ; ZERO WIDTH JOINER
                 (range #x20E3 #x20E3) ; COMBINING ENCLOSING KEYCAP
                 (range #xFE0F #xFE0F) ; VARIATION SELECTOR-16
                 (range #x1F1E6 #x1F1FF) ; the regional indicators
                 (range #x1F3FB #x1F3FF) ; the emoji modifiers
                 (range #x1F9B0 #x1F9B3) ; EMOJI COMPONENT RED HAIR to
                                         ; EMOJI COMPONENT WHITE HAIR
                 (range #xE0020 #xE007F)))) ; TAG SPACE to CANCEL TAG

  (defrule emoji-component-ranges-same-in-all-versions
    (equal (emoji-component-ranges ver1)
           (emoji-component-ranges ver2))
    :rule-classes nil
    :enable emoji-component-ranges-alt-def
    :disable emoji-component-ranges))

;;;;;;;;;;;;;;;;;;;;

(define emoji-component-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Emoji_Component') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (emoji-component-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extended-pictographic-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Extended_Pictographic') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *extended-pictographic-v16.0.0*
                :v17.0.0 *extended-pictographic-v17.0.0*
                :v18.0.0 *extended-pictographic-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define extended-pictographic-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Extended_Pictographic') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (extended-pictographic-ranges ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define regional-indicator-ranges ((ver versionp))
  :returns (ranges range-listp)
  :short "The ranges of the code points
          that have the @('Regional_Indicator') property,
          in a version of Unicode."
  (version-case ver
                :v16.0.0 *regional-indicator-v16.0.0*
                :v17.0.0 *regional-indicator-v17.0.0*
                :v18.0.0 *regional-indicator-v18.0.0*)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define regional-indicator-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point has the @('Regional_Indicator') property,
          in a version of Unicode."
  (code-point-in-ranges-p cp (regional-indicator-ranges ver))
  :hooks (:fix)

  ///

  (defruled regional-indicator-p-alt-def
    (equal (regional-indicator-p cp ver)
           (b* ((cp (code-point-fix cp)))
             (and (<= #x1F1E6 cp) ; REGIONAL INDICATOR SYMBOL LETTER A
                  (<= cp #x1F1FF)))) ; REGIONAL INDICATOR SYMBOL LETTER Z
    :enable (regional-indicator-ranges
             code-point-in-range-p))

  (defrule regional-indicator-p-same-in-all-versions
    (equal (regional-indicator-p cp ver1)
           (regional-indicator-p cp ver2))
    :rule-classes nil
    :enable regional-indicator-p-alt-def))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection emoji-theorems
  :short "Theorems that relate the emoji properties to each other,
          in every supported version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A code point that has @('Emoji_Presentation'), @('Emoji_Modifier')
     or @('Emoji_Modifier_Base') has @('Emoji'),
     and so does a regional indicator.
     A code point that has @('Emoji_Modifier_Base')
     has @('Extended_Pictographic').
     The modifiers and the regional indicators
     have @('Emoji_Component').
     A code point that has @('Emoji')
     has @('Extended_Pictographic') or @('Emoji_Component'):
     the emoji that are not pictographs are
     the number sign, the asterisk and the digits,
     the regional indicators, and the modifiers.")
   (xdoc::p
    "These are proved by evaluation on the tables, for each version:
     so adding a version checks them for that version."))

  (defrulel emoji-presentation-ranges-within-emoji-ranges
    (ranges-within-ranges-p (emoji-presentation-ranges ver)
                            (emoji-ranges ver))
    :enable (emoji-presentation-ranges emoji-ranges))

  (defrulel emoji-modifier-ranges-within-emoji-ranges
    (ranges-within-ranges-p (emoji-modifier-ranges ver)
                            (emoji-ranges ver))
    :enable (emoji-modifier-ranges emoji-ranges))

  (defrulel emoji-modifier-base-ranges-within-emoji-ranges
    (ranges-within-ranges-p (emoji-modifier-base-ranges ver)
                            (emoji-ranges ver))
    :enable (emoji-modifier-base-ranges emoji-ranges))

  (defrulel regional-indicator-ranges-within-emoji-ranges
    (ranges-within-ranges-p (regional-indicator-ranges ver)
                            (emoji-ranges ver))
    :enable (regional-indicator-ranges emoji-ranges))

  (defrulel emoji-modifier-base-ranges-within-extended-pictographic-ranges
    (ranges-within-ranges-p (emoji-modifier-base-ranges ver)
                            (extended-pictographic-ranges ver))
    :enable (emoji-modifier-base-ranges extended-pictographic-ranges))

  (defrule emoji-p-when-emoji-presentation-p
    (implies (emoji-presentation-p cp ver)
             (emoji-p cp ver))
    :enable (emoji-presentation-p
             emoji-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule emoji-p-when-emoji-modifier-p
    (implies (emoji-modifier-p cp ver)
             (emoji-p cp ver))
    :enable (emoji-modifier-p
             emoji-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule emoji-p-when-emoji-modifier-base-p
    (implies (emoji-modifier-base-p cp ver)
             (emoji-p cp ver))
    :enable (emoji-modifier-base-p
             emoji-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule emoji-p-when-regional-indicator-p
    (implies (regional-indicator-p cp ver)
             (emoji-p cp ver))
    :enable (regional-indicator-p
             emoji-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule extended-pictographic-p-when-emoji-modifier-base-p
    (implies (emoji-modifier-base-p cp ver)
             (extended-pictographic-p cp ver))
    :enable (emoji-modifier-base-p
             extended-pictographic-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrulel emoji-modifier-ranges-within-emoji-component-ranges
    (ranges-within-ranges-p (emoji-modifier-ranges ver)
                            (emoji-component-ranges ver))
    :enable (emoji-modifier-ranges emoji-component-ranges))

  (defrulel regional-indicator-ranges-within-emoji-component-ranges
    (ranges-within-ranges-p (regional-indicator-ranges ver)
                            (emoji-component-ranges ver))
    :enable (regional-indicator-ranges emoji-component-ranges))

  (defrule emoji-component-p-when-emoji-modifier-p
    (implies (emoji-modifier-p cp ver)
             (emoji-component-p cp ver))
    :enable (emoji-modifier-p
             emoji-component-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  (defrule emoji-component-p-when-regional-indicator-p
    (implies (regional-indicator-p cp ver)
             (emoji-component-p cp ver))
    :enable (regional-indicator-p
             emoji-component-p
             code-point-in-ranges-p-when-ranges-within-ranges-p))

  ;; The emoji that are neither pictographs nor components: there are none.

  (defrulel emoji-ranges-less-the-other-two
    (equal (ranges-difference (emoji-ranges ver)
                              (append (extended-pictographic-ranges ver)
                                      (emoji-component-ranges ver)))
           nil)
    :enable (emoji-ranges
             extended-pictographic-ranges
             emoji-component-ranges))

  (defruled extended-pictographic-p-or-emoji-component-p-when-emoji-p
    (implies (emoji-p cp ver)
             (or (extended-pictographic-p cp ver)
                 (emoji-component-p cp ver)))
    :enable (emoji-p
             extended-pictographic-p
             emoji-component-p)
    :use (:instance code-point-in-ranges-p-when-ranges-difference-is-empty
                    (ranges1 (emoji-ranges ver))
                    (ranges2 (append (extended-pictographic-ranges ver)
                                     (emoji-component-ranges ver))))))
