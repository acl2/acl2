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

(defxdoc+ general-category-tables
  :parents (tables)
  :short "The values of the @('General_Category') property,
          and tables of runs of code points that have the same value."
  :long
  (xdoc::topstring
   (xdoc::p
    "The @('General_Category') property assigns to every code point
     one of thirty values [UAX #44, Table 12].
     Unlike the properties whose tables are @(see maps),
     it has no value that most code points share
     and that a table could leave out.
     But code points that are next to each other
     often have the same value:
     in Unicode 17.0.0, the 1,114,112 code points
     form 4,144 runs of code points with the same value.")
   (xdoc::p
    "So we represent the property as a list of @(see runs).
     A run consists of a first code point, a last code point,
     and the value that every code point from the first to the last has.
     The generated tables list the runs in increasing order,
     and the runs cover every code point exactly once.
     That is a checkable property of a list of runs
     (see @(tsee general-category-run-list-covers-p)),
     and under it the value of a code point
     is the value of the one run that contains it.
     The type of the runs and the functions on lists of runs
     are introduced by the macro @(tsee defruns),
     which does the same for the other properties of this kind.")
   (xdoc::p
    "The code points that have a given value
     form a list of @(see ranges),
     which is obtained from the list of runs
     by keeping the runs with that value:
     see @(tsee general-category-run-list-ranges).
     The theorem
     @('code-point-in-general-category-run-list-ranges')
     relates the two views,
     so that what is proved or computed with lists of ranges
     applies to the values of the property."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(xdoc::without-xdoc
 (fty::deftagsum general-category
   (:uppercase-letter ())
   (:lowercase-letter ())
   (:titlecase-letter ())
   (:modifier-letter ())
   (:other-letter ())
   (:nonspacing-mark ())
   (:spacing-mark ())
   (:enclosing-mark ())
   (:decimal-number ())
   (:letter-number ())
   (:other-number ())
   (:connector-punctuation ())
   (:dash-punctuation ())
   (:open-punctuation ())
   (:close-punctuation ())
   (:initial-punctuation ())
   (:final-punctuation ())
   (:other-punctuation ())
   (:math-symbol ())
   (:currency-symbol ())
   (:modifier-symbol ())
   (:other-symbol ())
   (:space-separator ())
   (:line-separator ())
   (:paragraph-separator ())
   (:control ())
   (:format ())
   (:surrogate ())
   (:private-use ())
   (:unassigned ())
   :pred general-category-p))

(defxdoc general-category
  :parents (general-category-tables)
  :short "Fixtype of the values of the @('General_Category') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "The constructors are named after the long names of the values
     in the Unicode Character Database.
     The database also gives each value a two-letter abbreviation,
     which is what its files and most documentation use:
     see @(tsee general-category-abbreviation).
     The thirty values, in the order of [UAX #44, Table 12],
     with their abbreviations, are:")
   (xdoc::ul
    (xdoc::li "@('Lu'), @('Uppercase_Letter'): an uppercase letter.")
    (xdoc::li "@('Ll'), @('Lowercase_Letter'): a lowercase letter.")
    (xdoc::li "@('Lt'), @('Titlecase_Letter'):
               a character that stands for two letters,
               the first of them uppercase.")
    (xdoc::li "@('Lm'), @('Modifier_Letter'): a modifier letter.")
    (xdoc::li "@('Lo'), @('Other_Letter'):
               any other letter; syllables and ideographs are here.")
    (xdoc::li "@('Mn'), @('Nonspacing_Mark'):
               a combining mark that takes no space of its own.")
    (xdoc::li "@('Mc'), @('Spacing_Mark'):
               a combining mark that takes space.")
    (xdoc::li "@('Me'), @('Enclosing_Mark'):
               a combining mark that encloses what it applies to.")
    (xdoc::li "@('Nd'), @('Decimal_Number'): a decimal digit.")
    (xdoc::li "@('Nl'), @('Letter_Number'):
               a number written like a letter, such as a Roman numeral.")
    (xdoc::li "@('No'), @('Other_Number'): any other numeric character.")
    (xdoc::li "@('Pc'), @('Connector_Punctuation'):
               punctuation that connects, such as the underscore.")
    (xdoc::li "@('Pd'), @('Dash_Punctuation'): a dash or a hyphen.")
    (xdoc::li "@('Ps'), @('Open_Punctuation'):
               the opening character of a pair, such as a left bracket.")
    (xdoc::li "@('Pe'), @('Close_Punctuation'):
               the closing character of a pair.")
    (xdoc::li "@('Pi'), @('Initial_Punctuation'):
               an opening quotation mark.")
    (xdoc::li "@('Pf'), @('Final_Punctuation'):
               a closing quotation mark.")
    (xdoc::li "@('Po'), @('Other_Punctuation'): any other punctuation.")
    (xdoc::li "@('Sm'), @('Math_Symbol'): a mathematical symbol.")
    (xdoc::li "@('Sc'), @('Currency_Symbol'): a currency sign.")
    (xdoc::li "@('Sk'), @('Modifier_Symbol'):
               a modifier that is a symbol and not a letter.")
    (xdoc::li "@('So'), @('Other_Symbol'): any other symbol.")
    (xdoc::li "@('Zs'), @('Space_Separator'): a space character.")
    (xdoc::li "@('Zl'), @('Line_Separator'):
               the one character U+2028 LINE SEPARATOR.")
    (xdoc::li "@('Zp'), @('Paragraph_Separator'):
               the one character U+2029 PARAGRAPH SEPARATOR.")
    (xdoc::li "@('Cc'), @('Control'): a control code.")
    (xdoc::li "@('Cf'), @('Format'): a format control character.")
    (xdoc::li "@('Cs'), @('Surrogate'): a surrogate code point.")
    (xdoc::li "@('Co'), @('Private_Use'): a private-use code point.")
    (xdoc::li "@('Cn'), @('Unassigned'):
               a code point that has no character assigned to it,
               which is either reserved for future assignment
               or a noncharacter."))
   (xdoc::p
    "The first letter of an abbreviation
     is the same for values that belong together:
     see @(tsee general-category-letter-p)
     and the predicates that follow it.")
   (xdoc::p
    "The type is introduced with @(tsee fty::deftagsum).
     Each value has a constructor without arguments,
     named @('general-category-') followed by the long name of the value
     in lower case, with hyphens in place of underscores:
     for example, @('(general-category-uppercase-letter)').
     The recognizer of the type is @('general-category-p'),
     its fixer is @('general-category-fix'),
     and its equivalence is @('general-category-equiv').
     The function @('general-category-kind')
     returns the keyword of a value, such as @(':uppercase-letter'),
     and the macro @('general-category-case')
     distinguishes the values by their keywords.")
   (xdoc::p
    "Apart from the recognizer, which has a topic of one line
     so that the signatures of functions link to this type,
     these functions and macros have no documentation topics of their own.
     @(tsee fty::deftagsum) generates 96 topics for this type,
     three of them for each value,
     and none of them would say more than this topic does.
     So we turn them off, with @('xdoc::without-xdoc').")))

(defxdoc general-category-p
  :parents (general-category)
  :short "Recognizer of the values of the type @(tsee general-category).")

;;;;;;;;;;;;;;;;;;;;

(define general-category-abbreviation ((gc general-category-p))
  :returns (abbreviation stringp)
  :short "The two-letter abbreviation of
          a value of the @('General_Category') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the short alias of the value
     in the file @('PropertyValueAliases.txt')
     of the Unicode Character Database."))
  (general-category-case gc
                         :uppercase-letter "Lu"
                         :lowercase-letter "Ll"
                         :titlecase-letter "Lt"
                         :modifier-letter "Lm"
                         :other-letter "Lo"
                         :nonspacing-mark "Mn"
                         :spacing-mark "Mc"
                         :enclosing-mark "Me"
                         :decimal-number "Nd"
                         :letter-number "Nl"
                         :other-number "No"
                         :connector-punctuation "Pc"
                         :dash-punctuation "Pd"
                         :open-punctuation "Ps"
                         :close-punctuation "Pe"
                         :initial-punctuation "Pi"
                         :final-punctuation "Pf"
                         :other-punctuation "Po"
                         :math-symbol "Sm"
                         :currency-symbol "Sc"
                         :modifier-symbol "Sk"
                         :other-symbol "So"
                         :space-separator "Zs"
                         :line-separator "Zl"
                         :paragraph-separator "Zp"
                         :control "Cc"
                         :format "Cf"
                         :surrogate "Cs"
                         :private-use "Co"
                         :unassigned "Cn")
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(fty::deflist general-category-list
  :short "Fixtype of lists of values of the @('General_Category') property."
  :elt-type general-category
  :true-listp t
  :elementp-of-nil nil
  :pred general-category-listp)

;;;;;;;;;;;;;;;;;;;;

(define general-category-values ()
  :returns (gcs general-category-listp)
  :short "The thirty values of the @('General_Category') property."
  :long
  (xdoc::topstring
   (xdoc::p
    "They are in the order of [UAX #44, Table 12],
     which is the order in @(tsee general-category).
     Every value is in the list, once."))
  (list (general-category-uppercase-letter)
        (general-category-lowercase-letter)
        (general-category-titlecase-letter)
        (general-category-modifier-letter)
        (general-category-other-letter)
        (general-category-nonspacing-mark)
        (general-category-spacing-mark)
        (general-category-enclosing-mark)
        (general-category-decimal-number)
        (general-category-letter-number)
        (general-category-other-number)
        (general-category-connector-punctuation)
        (general-category-dash-punctuation)
        (general-category-open-punctuation)
        (general-category-close-punctuation)
        (general-category-initial-punctuation)
        (general-category-final-punctuation)
        (general-category-other-punctuation)
        (general-category-math-symbol)
        (general-category-currency-symbol)
        (general-category-modifier-symbol)
        (general-category-other-symbol)
        (general-category-space-separator)
        (general-category-line-separator)
        (general-category-paragraph-separator)
        (general-category-control)
        (general-category-format)
        (general-category-surrogate)
        (general-category-private-use)
        (general-category-unassigned))

  ///

  (defrule len-of-general-category-values
    (equal (len (general-category-values))
           30))

  (defrule no-duplicatesp-equal-of-general-category-values
    (no-duplicatesp-equal (general-category-values)))

  (defrule member-equal-of-general-category-fix-and-values
    (member-equal (general-category-fix gc) (general-category-values))
    :use (:instance general-category-kind-possibilities (x gc))
    :disable (general-category-values
              general-category-kind-possibilities))

  (defrulel general-category-p-when-member-equal-of-values
    (implies (member-equal gc (general-category-values))
             (general-category-p gc))
    :enable member-equal)

  (in-theory (disable (:e general-category-values)))

  (defrule member-equal-of-general-category-values
    (iff (member-equal gc (general-category-values))
         (general-category-p gc))
    :disable (general-category-values
              member-equal-of-general-category-fix-and-values)
    :use member-equal-of-general-category-fix-and-values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define general-category-letter-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the five values for letters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Lu'), @('Ll'), @('Lt'), @('Lm') and @('Lo'),
     which together are called @('L') or @('Letter')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :uppercase-letter t
                         :lowercase-letter t
                         :titlecase-letter t
                         :modifier-letter t
                         :other-letter t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-cased-letter-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the three values for cased letters."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Lu'), @('Ll') and @('Lt'),
     which together are called @('LC') or @('Cased_Letter')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :uppercase-letter t
                         :lowercase-letter t
                         :titlecase-letter t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-mark-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the three values for combining marks."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Mn'), @('Mc') and @('Me'),
     which together are called @('M') or @('Mark')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :nonspacing-mark t
                         :spacing-mark t
                         :enclosing-mark t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-number-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the three values for numbers."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Nd'), @('Nl') and @('No'),
     which together are called @('N') or @('Number')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :decimal-number t
                         :letter-number t
                         :other-number t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-punctuation-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the seven values for punctuation."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Pc'), @('Pd'), @('Ps'), @('Pe'),
     @('Pi'), @('Pf') and @('Po'),
     which together are called @('P') or @('Punctuation')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :connector-punctuation t
                         :dash-punctuation t
                         :open-punctuation t
                         :close-punctuation t
                         :initial-punctuation t
                         :final-punctuation t
                         :other-punctuation t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-symbol-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the four values for symbols."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Sm'), @('Sc'), @('Sk') and @('So'),
     which together are called @('S') or @('Symbol')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :math-symbol t
                         :currency-symbol t
                         :modifier-symbol t
                         :other-symbol t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-separator-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the three values for separators."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Zs'), @('Zl') and @('Zp'),
     which together are called @('Z') or @('Separator')
     [UAX #44, Table 12]."))
  (general-category-case gc
                         :space-separator t
                         :line-separator t
                         :paragraph-separator t
                         :otherwise nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-other-p ((gc general-category-p))
  :returns (yes/no booleanp)
  :short "Check if a value of the @('General_Category') property
          is one of the five remaining values."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are @('Cc'), @('Cf'), @('Cs'), @('Co') and @('Cn'),
     which together are called @('C') or @('Other')
     [UAX #44, Table 12]:
     they are the values of the code points
     that are neither letters, marks, numbers, punctuation,
     symbols nor separators.")
   (xdoc::p
    "Each value satisfies exactly one of this predicate,
     @(tsee general-category-letter-p),
     @(tsee general-category-mark-p),
     @(tsee general-category-number-p),
     @(tsee general-category-punctuation-p),
     @(tsee general-category-symbol-p) and
     @(tsee general-category-separator-p):
     see the theorem @('general-category-major-classes')."))
  (general-category-case gc
                         :control t
                         :format t
                         :surrogate t
                         :private-use t
                         :unassigned t
                         :otherwise nil)
  :hooks (:fix)

  ///

  (defruled general-category-major-classes
    (equal (+ (if (general-category-letter-p gc) 1 0)
              (if (general-category-mark-p gc) 1 0)
              (if (general-category-number-p gc) 1 0)
              (if (general-category-punctuation-p gc) 1 0)
              (if (general-category-symbol-p gc) 1 0)
              (if (general-category-separator-p gc) 1 0)
              (if (general-category-other-p gc) 1 0))
           1)
    :enable (general-category-letter-p
             general-category-mark-p
             general-category-number-p
             general-category-punctuation-p
             general-category-symbol-p
             general-category-separator-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruns general-category
  :property "General_Category"
  :value-type general-category
  :value-pred general-category-p
  :value-fix general-category-fix
  :default (general-category-unassigned))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection general-category-run-table
  :short "Write a list of runs of @('General_Category') compactly."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each run is written as a triple
     of the minimum code point, the maximum code point,
     and the two-letter abbreviation of the value, as a string
     (see @(tsee general-category-abbreviation)):")
   (xdoc::codeblock
    "(general-category-run-table"
    " (#x0041 #x005A \"Lu\")"
    " (#x005B #x005B \"Ps\"))")
   (xdoc::p
    "See @(see run-tables) for what this expands to.
     The generated tables have some four thousand runs each."))

  (defconst *general-category-constructors*
    '(("Lu" . general-category-uppercase-letter)
      ("Ll" . general-category-lowercase-letter)
      ("Lt" . general-category-titlecase-letter)
      ("Lm" . general-category-modifier-letter)
      ("Lo" . general-category-other-letter)
      ("Mn" . general-category-nonspacing-mark)
      ("Mc" . general-category-spacing-mark)
      ("Me" . general-category-enclosing-mark)
      ("Nd" . general-category-decimal-number)
      ("Nl" . general-category-letter-number)
      ("No" . general-category-other-number)
      ("Pc" . general-category-connector-punctuation)
      ("Pd" . general-category-dash-punctuation)
      ("Ps" . general-category-open-punctuation)
      ("Pe" . general-category-close-punctuation)
      ("Pi" . general-category-initial-punctuation)
      ("Pf" . general-category-final-punctuation)
      ("Po" . general-category-other-punctuation)
      ("Sm" . general-category-math-symbol)
      ("Sc" . general-category-currency-symbol)
      ("Sk" . general-category-modifier-symbol)
      ("So" . general-category-other-symbol)
      ("Zs" . general-category-space-separator)
      ("Zl" . general-category-line-separator)
      ("Zp" . general-category-paragraph-separator)
      ("Cc" . general-category-control)
      ("Cf" . general-category-format)
      ("Cs" . general-category-surrogate)
      ("Co" . general-category-private-use)
      ("Cn" . general-category-unassigned)))

  (defmacro general-category-run-table (&rest triples)
    `(list ,@(run-table-forms triples
                              :value
                              *general-category-constructors*
                              'general-category-run
                              'general-category-run-table))))
