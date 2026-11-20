; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "runs")

(include-book "xdoc/alter" :dir :system) ; for XDOC::WITHOUT-XDOC

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-class-tables
  :parents (tables)
  :short "The values of the @('Bidi_Class') property,
          and tables of runs of code points that have the same value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('Bidi_Class') property assigns to every code point
     one of twenty-three bidirectional classes [UAX #9, Table 4],
     which are what the Unicode Bidirectional Algorithm
     knows about a character.
     The property is represented as a list of @(see runs)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::without-xdoc
 (fty::deftagsum bidi-class
   (:left-to-right ())
   (:right-to-left ())
   (:arabic-letter ())
   (:european-number ())
   (:european-separator ())
   (:european-terminator ())
   (:arabic-number ())
   (:common-separator ())
   (:nonspacing-mark ())
   (:boundary-neutral ())
   (:paragraph-separator ())
   (:segment-separator ())
   (:white-space ())
   (:other-neutral ())
   (:left-to-right-embedding ())
   (:left-to-right-override ())
   (:right-to-left-embedding ())
   (:right-to-left-override ())
   (:pop-directional-format ())
   (:left-to-right-isolate ())
   (:right-to-left-isolate ())
   (:first-strong-isolate ())
   (:pop-directional-isolate ())
   :pred bidi-class-p))

(defxdoc bidi-class
  :parents (bidi-class-tables)
  :short "Fixtype of the values of the @('Bidi_Class') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each value has a long name, which we use for the value,
     and an abbreviation of one to three letters,
     which the files of the Unicode Character Database
     and most documentation use:
     see @(tsee bidi-class-abbreviation).
     The twenty-three values, in the order of [UAX #9, Table 4],
     with their abbreviations, are as follows.")
   (xdoc::p
    "The strong classes:")
   (xdoc::ul
    (xdoc::li "@('L'), @('Left_To_Right'):
               a character of a script written from left to right.")
    (xdoc::li "@('R'), @('Right_To_Left'):
               a character of a script written from right to left,
               other than those of the next class.")
    (xdoc::li "@('AL'), @('Arabic_Letter'):
               a letter of Arabic or of another script
               in which numbers are treated as in Arabic."))
   (xdoc::p
    "The weak classes:")
   (xdoc::ul
    (xdoc::li "@('EN'), @('European_Number'): a European digit.")
    (xdoc::li "@('ES'), @('European_Separator'): a plus or minus sign.")
    (xdoc::li "@('ET'), @('European_Terminator'):
               a sign that goes with a number, such as a currency sign.")
    (xdoc::li "@('AN'), @('Arabic_Number'): an Arabic-Indic digit.")
    (xdoc::li "@('CS'), @('Common_Separator'):
               a separator inside numbers, such as the comma.")
    (xdoc::li "@('NSM'), @('Nonspacing_Mark'): a nonspacing mark.")
    (xdoc::li "@('BN'), @('Boundary_Neutral'):
               a character that the algorithm ignores,
               such as most format controls."))
   (xdoc::p
    "The neutral classes:")
   (xdoc::ul
    (xdoc::li "@('B'), @('Paragraph_Separator').")
    (xdoc::li "@('S'), @('Segment_Separator'): a tab.")
    (xdoc::li "@('WS'), @('White_Space'): a space.")
    (xdoc::li "@('ON'), @('Other_Neutral'):
               any other character without a direction of its own,
               such as most punctuation and symbols."))
   (xdoc::p
    "The classes of the explicit directional formatting characters:")
   (xdoc::ul
    (xdoc::li "@('LRE'), @('Left_To_Right_Embedding').")
    (xdoc::li "@('LRO'), @('Left_To_Right_Override').")
    (xdoc::li "@('RLE'), @('Right_To_Left_Embedding').")
    (xdoc::li "@('RLO'), @('Right_To_Left_Override').")
    (xdoc::li "@('PDF'), @('Pop_Directional_Format'),
               which ends an embedding or an override.")
    (xdoc::li "@('LRI'), @('Left_To_Right_Isolate').")
    (xdoc::li "@('RLI'), @('Right_To_Left_Isolate').")
    (xdoc::li "@('FSI'), @('First_Strong_Isolate').")
    (xdoc::li "@('PDI'), @('Pop_Directional_Isolate'),
               which ends an isolate."))
   (xdoc::p
    "The type is introduced with @(tsee fty::deftagsum).
     Each value has a constructor without arguments,
     named @('bidi-class-') followed by the long name of the value
     in lower case, with hyphens in place of underscores:
     for example, @('(bidi-class-left-to-right)').
     The recognizer of the type is @('bidi-class-p'),
     its fixer is @('bidi-class-fix'),
     and its equivalence is @('bidi-class-equiv').
     The function @('bidi-class-kind')
     returns the keyword of a value, such as @(':left-to-right'),
     and the macro @('bidi-class-case')
     distinguishes the values by their keywords.")
   (xdoc::p
    "These functions and macros have no documentation topics of their own.
     @(tsee fty::deftagsum) generates 75 topics for this type,
     three of them for each value,
     and none of them would say more than this topic does.
     So we turn them off, with @('xdoc::without-xdoc').")))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-abbreviation ((class bidi-class-p))
  :returns (abbreviation stringp)
  :short "The abbreviation of a value of the @('Bidi_Class') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the short name of the value
     in the file @('PropertyValueAliases.txt')
     of the Unicode Character Database."))
  (bidi-class-case class
                   :left-to-right "L"
                   :right-to-left "R"
                   :arabic-letter "AL"
                   :european-number "EN"
                   :european-separator "ES"
                   :european-terminator "ET"
                   :arabic-number "AN"
                   :common-separator "CS"
                   :nonspacing-mark "NSM"
                   :boundary-neutral "BN"
                   :paragraph-separator "B"
                   :segment-separator "S"
                   :white-space "WS"
                   :other-neutral "ON"
                   :left-to-right-embedding "LRE"
                   :left-to-right-override "LRO"
                   :right-to-left-embedding "RLE"
                   :right-to-left-override "RLO"
                   :pop-directional-format "PDF"
                   :left-to-right-isolate "LRI"
                   :right-to-left-isolate "RLI"
                   :first-strong-isolate "FSI"
                   :pop-directional-isolate "PDI")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-class-strong-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is a strong class."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strong classes are @('Left_To_Right'), @('Right_To_Left')
     and @('Arabic_Letter') [UAX #9, Table 4]:
     the classes of the characters that have a direction of their own."))
  (bidi-class-case class
                   :left-to-right t
                   :right-to-left t
                   :arabic-letter t
                   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-right-to-left-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class
          is @('Right_To_Left') or @('Arabic_Letter')."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the two strong classes
     of the characters that are written from right to left.
     A text that has no character of these two classes
     and no explicit directional formatting character
     is displayed from left to right, in the order in which it is stored."))
  (bidi-class-case class
                   :right-to-left t
                   :arabic-letter t
                   :otherwise nil)
  :hooks (:fix)

  ///

  (defrule bidi-class-strong-p-when-bidi-class-right-to-left-p
    (implies (bidi-class-right-to-left-p class)
             (bidi-class-strong-p class))
    :enable bidi-class-strong-p))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-weak-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is a weak class."
  :long
  (xdoc::topstring
   (xdoc::p
    "The weak classes are those of the digits,
     of the characters that go with numbers,
     of the nonspacing marks,
     and of the characters that the algorithm ignores
     [UAX #9, Table 4]."))
  (bidi-class-case class
                   :european-number t
                   :european-separator t
                   :european-terminator t
                   :arabic-number t
                   :common-separator t
                   :nonspacing-mark t
                   :boundary-neutral t
                   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-neutral-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is a neutral class."
  :long
  (xdoc::topstring
   (xdoc::p
    "The neutral classes are those of the separators,
     of the spaces and of the other characters
     without a direction of their own [UAX #9, Table 4]."))
  (bidi-class-case class
                   :paragraph-separator t
                   :segment-separator t
                   :white-space t
                   :other-neutral t
                   :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-class-explicit-formatting-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  :short "Check if a bidirectional class is one of the nine classes
          of the explicit directional formatting characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the classes of the embeddings, the overrides, the isolates
     and the characters that end them
     [UAX #9, Table 4, Sections 2.1 to 2.5].
     Every class is strong, weak, neutral or one of these, and only one:
     see the theorem @('bidi-class-kinds')."))
  (bidi-class-case class
                   :left-to-right-embedding t
                   :left-to-right-override t
                   :right-to-left-embedding t
                   :right-to-left-override t
                   :pop-directional-format t
                   :left-to-right-isolate t
                   :right-to-left-isolate t
                   :first-strong-isolate t
                   :pop-directional-isolate t
                   :otherwise nil)
  :hooks (:fix)

  ///

  (defruled bidi-class-kinds
    (equal (+ (if (bidi-class-strong-p class) 1 0)
              (if (bidi-class-weak-p class) 1 0)
              (if (bidi-class-neutral-p class) 1 0)
              (if (bidi-class-explicit-formatting-p class) 1 0))
           1)
    :enable (bidi-class-strong-p
             bidi-class-weak-p
             bidi-class-neutral-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruns bidi-class
  :property "Bidi_Class"
  :value-type bidi-class
  :value-pred bidi-class-p
  :value-fix bidi-class-fix
  :default (bidi-class-left-to-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-class-run-table
  :short "Write a list of runs of @('Bidi_Class') compactly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each run is written as a triple
     of the minimum code point, the maximum code point,
     and the abbreviation of the class, as a string
     (see @(tsee bidi-class-abbreviation)):")
   (xdoc::codeblock
    "(bidi-class-run-table"
    " (#x0041 #x005A \"L\")"
    " (#x005B #x0060 \"ON\"))")
   (xdoc::p
    "See @(see run-tables) for what this expands to."))

  (defconst *bidi-class-constructors*
    '(("L" . bidi-class-left-to-right)
      ("R" . bidi-class-right-to-left)
      ("AL" . bidi-class-arabic-letter)
      ("EN" . bidi-class-european-number)
      ("ES" . bidi-class-european-separator)
      ("ET" . bidi-class-european-terminator)
      ("AN" . bidi-class-arabic-number)
      ("CS" . bidi-class-common-separator)
      ("NSM" . bidi-class-nonspacing-mark)
      ("BN" . bidi-class-boundary-neutral)
      ("B" . bidi-class-paragraph-separator)
      ("S" . bidi-class-segment-separator)
      ("WS" . bidi-class-white-space)
      ("ON" . bidi-class-other-neutral)
      ("LRE" . bidi-class-left-to-right-embedding)
      ("LRO" . bidi-class-left-to-right-override)
      ("RLE" . bidi-class-right-to-left-embedding)
      ("RLO" . bidi-class-right-to-left-override)
      ("PDF" . bidi-class-pop-directional-format)
      ("LRI" . bidi-class-left-to-right-isolate)
      ("RLI" . bidi-class-right-to-left-isolate)
      ("FSI" . bidi-class-first-strong-isolate)
      ("PDI" . bidi-class-pop-directional-isolate)))

  (defmacro bidi-class-run-table (&rest triples)
    `(list ,@(run-table-forms triples
                              :value
                              *bidi-class-constructors*
                              'bidi-class-run
                              'bidi-class-run-table))))
