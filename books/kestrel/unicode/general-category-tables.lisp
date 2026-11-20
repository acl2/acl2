; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "ranges")

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
    "So we represent the property as a list of runs.
     A run consists of a first code point, a last code point,
     and the value that every code point from the first to the last has.
     The generated tables list the runs in increasing order,
     and the runs cover every code point exactly once.
     That is a checkable property of a list of runs
     (see @(tsee general-category-run-list-covers-p)),
     and under it the value of a code point
     is the value of the one run that contains it.")
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

(fty::deftagsum general-category
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
     and the predicates that follow it."))
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
  :pred general-category-p)

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

(fty::defprod general-category-run
  :short "Fixtype of runs of code points
          that have the same @('General_Category')."
  :long
  (xdoc::topstring
   (xdoc::p
    "A run consists of a minimum and a maximum code point,
     and a value of the @('General_Category') property.
     It says that the code points
     from the minimum to the maximum, both included,
     have that value."))
  ((min code-point)
   (max code-point)
   (value general-category))
  :pred general-category-run-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist general-category-run-list
  :short "Fixtype of lists of runs of code points
          that have the same @('General_Category')."
  :elt-type general-category-run
  :true-listp t
  :elementp-of-nil nil
  :pred general-category-run-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define general-category-run-list-lookup ((cp code-point-p)
                                          (runs general-category-run-listp))
  :returns (gc general-category-p)
  :short "The @('General_Category') that a list of runs gives to a code point."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the value of the first run of the list
     that contains the code point.
     If no run contains the code point,
     the result is @('Unassigned'),
     which is the default value of the property [UAX #44];
     that case does not arise with the generated tables,
     whose runs cover every code point."))
  (cond ((endp runs) (general-category-unassigned))
        (t (b* (((general-category-run run) (car runs))
                (fixed-cp (code-point-fix cp)))
             (if (and (<= run.min fixed-cp)
                      (<= fixed-cp run.max))
                 run.value
               (general-category-run-list-lookup cp (cdr runs))))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-run-list-ranges ((gc general-category-p)
                                          (runs general-category-run-listp))
  :returns (ranges range-listp)
  :short "The ranges of the runs of a list
          that have a given @('General_Category')."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result has one range for each run with that value,
     in the same order."))
  (cond ((endp runs) nil)
        (t (b* (((general-category-run run) (car runs))
                (ranges (general-category-run-list-ranges gc (cdr runs))))
             (if (equal run.value (general-category-fix gc))
                 (cons (range run.min run.max) ranges)
               ranges))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define general-category-run-list-covers-p ((min code-point-p)
                                            (max code-point-p)
                                            (runs general-category-run-listp))
  :returns (yes/no booleanp)
  :short "Check if the runs of a list cover, in order and exactly once,
          the code points from a minimum to a maximum."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is: the first run starts at the minimum,
     each run after it starts
     right after the one before it ends,
     the last run ends at the maximum,
     and no run is empty.
     In particular the list has at least one run.")
   (xdoc::p
    "Each generated table satisfies this predicate
     with the minimum 0 and the maximum @('#x10FFFF'),
     which is checked by evaluation in the book that has the table.
     Then every code point is in exactly one run,
     and the theorem
     @('code-point-in-general-category-run-list-ranges')
     applies to every code point."))
  (b* (((when (endp runs)) nil)
       ((general-category-run run) (car runs))
       (min (code-point-fix min))
       (max (code-point-fix max))
       ((unless (and (equal run.min min)
                     (<= run.min run.max)))
        nil)
       ((when (endp (cdr runs))) (equal run.max max)))
    (and (< run.max max)
         (general-category-run-list-covers-p (+ 1 run.max) max (cdr runs))))
  :guard-hints (("Goal" :in-theory (enable code-point-p)))
  :measure (acl2-count runs)
  :hooks (:fix)

  ///

  (defrulel code-point-fix-upper-bound
    (<= (code-point-fix x) #x10FFFF)
    :rule-classes :linear
    :enable (code-point-fix code-point-p))

  (defruled general-category-run-list-lookup-when-in-ranges
    (implies (and (general-category-run-list-covers-p min max runs)
                  (code-point-in-ranges-p
                   cp (general-category-run-list-ranges gc runs)))
             (and (<= (code-point-fix min) (code-point-fix cp))
                  (equal (general-category-run-list-lookup cp runs)
                         (general-category-fix gc))))
    :induct (general-category-run-list-covers-p min max runs)
    :enable (general-category-run-list-lookup
             general-category-run-list-ranges
             code-point-in-range-p
             code-point-p))

  (defruled in-general-category-run-list-ranges-when-lookup
    (implies (and (general-category-run-list-covers-p min max runs)
                  (<= (code-point-fix min) (code-point-fix cp))
                  (<= (code-point-fix cp) (code-point-fix max))
                  (equal (general-category-run-list-lookup cp runs)
                         (general-category-fix gc)))
             (code-point-in-ranges-p
              cp (general-category-run-list-ranges gc runs)))
    :induct (general-category-run-list-covers-p min max runs)
    :enable (general-category-run-list-lookup
             general-category-run-list-ranges
             code-point-in-range-p
             code-point-p))

  (defruled code-point-in-general-category-run-list-ranges-when-between
    (implies (and (general-category-run-list-covers-p min max runs)
                  (<= (code-point-fix min) (code-point-fix cp))
                  (<= (code-point-fix cp) (code-point-fix max)))
             (equal (code-point-in-ranges-p
                     cp (general-category-run-list-ranges gc runs))
                    (equal (general-category-run-list-lookup cp runs)
                           (general-category-fix gc))))
    :enable (general-category-run-list-lookup-when-in-ranges
             in-general-category-run-list-ranges-when-lookup))

  (defruled code-point-in-general-category-run-list-ranges
    (implies (general-category-run-list-covers-p 0 #x10FFFF runs)
             (equal (code-point-in-ranges-p
                     cp (general-category-run-list-ranges gc runs))
                    (equal (general-category-run-list-lookup cp runs)
                           (general-category-fix gc))))
    :enable code-point-in-general-category-run-list-ranges-when-between))
