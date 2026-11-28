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
(include-book "scripts")
(include-book "range-operations")

(include-book "std/lists/flatten" :dir :system)

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ identifier-word-boundaries
  :parents (unicode)
  :short "The chunks of an identifier:
          the words that its letter case and its punctuation make visible."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unicode Source Code Handling [UTS #55, Section 5.1.2.1]
     cuts an identifier into chunks,
     which are what a reader sees as its words:
     @('HTTPRequest') is @('HTTP') and @('Request'),
     and @('loud_snake') is @('loud'), @('_') and @('snake').
     The specification does this so that mixed-script detection
     (see @(see mixed-script-detection))
     can be applied to each chunk and not to the whole identifier,
     since an identifier may well have words in two scripts.")
   (xdoc::p
    "The chunks are delimited by identifier word boundaries.
     There are three rules for where a boundary is.
     In them, a letter followed by nonspacing or enclosing marks
     counts as that letter;
     the letters are told apart by their @('General_Category')
     (see @(see general-category-property)):
     @('Lu') is an uppercase letter,
     @('Ll') a lowercase letter,
     and @('Lt') a titlecase letter,
     which is a character for two letters
     of which the first is uppercase, such as U+01C5.")
   (xdoc::ol
    (xdoc::li
     "There is a boundary after a lowercase letter,
      or a titlecase letter that is not Greek,
      that is followed by an uppercase or titlecase letter.
      The specification calls it a camel boundary.")
    (xdoc::li
     "There is a boundary before an uppercase or titlecase letter
      that is followed by a lowercase letter,
      and before a titlecase letter that is not Greek.
      The specification calls it a hat boundary;
      it keeps an acronym in upper case apart from the word after it.")
    (xdoc::li
     "There is a boundary before and after a punctuation character
      whose @('General_Category') is not @('Po') (@('Other_Punctuation')).
      The specification calls it a snake boundary.
      The low line and the hyphen are such characters."))
   (xdoc::p
    "There is no other boundary.
     The specification does not say why
     the Greek titlecase letters are excepted.
     In the three versions of Unicode that this library has,
     there are thirty-one titlecase letters.
     Four are Latin, U+01C5, U+01C8, U+01CB and U+01F2,
     and each is two letters in one character
     (U+01C5 is a capital D and a small z with a caron).
     The other twenty-seven are Greek,
     and each is one capital letter
     with a iota written beside it (prosgegrammeni), such as U+1F88:
     there is no second word that starts inside it.")
   (xdoc::p
    "The rules use only the @('General_Category') of the characters
     and whether the @('Script') of a titlecase letter is Greek.
     They do not use the properties @('Lowercase') and @('Uppercase')
     or the case mappings, which this library does not have.")
   (xdoc::p
    "What the specification then asks about a chunk,
     namely whether it is confusing [UTS #55, Section 5.1.2.2],
     is not here:
     it needs the restriction levels of [UTS #39, Section 5.2]
     and a search among all the strings
     that are confusable with the chunk."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define chunk-mark-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a nonspacing or enclosing mark,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is
     @('Mn') (@('Nonspacing_Mark')) or @('Me') (@('Enclosing_Mark')).
     The rules for identifier word boundaries skip these marks."))
  (b* ((gc (code-point-general-category cp ver)))
    (general-category-case gc
                           :nonspacing-mark t
                           :enclosing-mark t
                           :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define chunk-lowercase-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a lowercase letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is
     @('Ll') (@('Lowercase_Letter'))."))
  (equal (general-category-kind (code-point-general-category cp ver))
         :lowercase-letter)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define chunk-uppercase-or-titlecase-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is an uppercase or titlecase letter,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is
     @('Lu') (@('Uppercase_Letter')) or @('Lt') (@('Titlecase_Letter'))."))
  (b* ((gc (code-point-general-category cp ver)))
    (general-category-case gc
                           :uppercase-letter t
                           :titlecase-letter t
                           :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define chunk-non-greek-titlecase-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a titlecase letter that is not Greek,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is
     @('Lt') (@('Titlecase_Letter'))
     and its @('Script') is not @('Greek').
     In the supported versions these are four Latin characters:
     U+01C5, U+01C8, U+01CB and U+01F2.")
   (xdoc::p
    "The specification writes @('\\p{Grek}') for the Greek characters,
     which can be read as a condition on the @('Script') property
     or on the @('Script_Extensions') property.
     For a titlecase letter the two are the same:
     see @(tsee script-extensions-of-titlecase-letter)."))
  (and (equal (general-category-kind (code-point-general-category cp ver))
              :titlecase-letter)
       (not (equal (code-point-script cp ver)
                   (script-greek))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define chunk-punctuation-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is punctuation
          other than @('Other_Punctuation'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is one of
     @('Pc') (@('Connector_Punctuation')),
     @('Pd') (@('Dash_Punctuation')),
     @('Ps') (@('Open_Punctuation')),
     @('Pe') (@('Close_Punctuation')),
     @('Pi') (@('Initial_Punctuation'))
     and @('Pf') (@('Final_Punctuation'))."))
  (b* ((gc (code-point-general-category cp ver)))
    (general-category-case gc
                           :connector-punctuation t
                           :dash-punctuation t
                           :open-punctuation t
                           :close-punctuation t
                           :initial-punctuation t
                           :final-punctuation t
                           :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define chunk-skip-marks ((cps code-point-listp) (ver versionp))
  :returns (rest code-point-listp)
  :short "Remove the nonspacing and enclosing marks
          at the start of a list of code points,
          in a version of Unicode."
  (cond ((endp cps) nil)
        ((chunk-mark-p (car cps) ver) (chunk-skip-marks (cdr cps) ver))
        (t (code-point-list-fix cps)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-word-boundary-p ((before code-point-listp)
                                    (after code-point-listp)
                                    (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if there is an identifier word boundary
          at a position in a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The position is given by the code points before it,
     in reverse order, so that the nearest one is first,
     and by the code points after it, in order.
     Either list can be empty:
     the position is then the start or the end of the text.")
   (xdoc::p
    "These are the three rules of [UTS #55, Section 5.1.2.1]:
     see @(see identifier-word-boundaries).
     The first rule needs a character on each side of the position.
     The second rule looks only at the characters after the position,
     and the third rule at the character on one side of it.
     So there can be a boundary at the start of the text,
     by the second rule or by the third:
     the table of examples of the specification
     marks one at the start of @('TypeII').
     There can be one at the end of the text, by the third rule.
     A boundary at the start or at the end of the text
     delimits no chunk: see @(tsee identifier-chunks)."))
  (b* ((base? (chunk-skip-marks before ver))
       (camel (and (consp base?)
                   (consp after)
                   (or (chunk-lowercase-p (car base?) ver)
                       (chunk-non-greek-titlecase-p (car base?) ver))
                   (chunk-uppercase-or-titlecase-p (car after) ver)))
       (following? (and (consp after)
                        (chunk-skip-marks (cdr after) ver)))
       (hat (and (consp after)
                 (or (chunk-non-greek-titlecase-p (car after) ver)
                     (and (chunk-uppercase-or-titlecase-p (car after) ver)
                          (consp following?)
                          (chunk-lowercase-p (car following?) ver)))))
       (snake (or (and (consp after)
                       (chunk-punctuation-p (car after) ver))
                  (and (consp before)
                       (chunk-punctuation-p (car before) ver)))))
    (or camel hat snake))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define identifier-chunks-from ((before code-point-listp)
                                (after code-point-listp)
                                (ver versionp))
  :returns (chunks code-point-list-listp)
  :short "The chunks of the part of a list of code points
          that is after a position,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are as in @(tsee identifier-word-boundary-p).
     The first chunk starts at the position,
     whether there is a boundary there or not."))
  (b* (((when (endp after)) nil)
       (cp (code-point-fix (car after)))
       (before (cons cp (code-point-list-fix before)))
       (chunks (identifier-chunks-from before (cdr after) ver))
       ((when (or (endp chunks)
                  (identifier-word-boundary-p before (cdr after) ver)))
        (cons (list cp) chunks)))
    (cons (cons cp (car chunks))
          (cdr chunks)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defrule consp-of-identifier-chunks-from
    (equal (consp (identifier-chunks-from before after ver))
           (consp after))
    :induct t)

  (defrule flatten-of-identifier-chunks-from
    (equal (acl2::flatten (identifier-chunks-from before after ver))
           (code-point-list-fix after))
    :induct t
    :enable acl2::flatten)

  (defrule not-member-equal-of-nil-and-identifier-chunks-from
    (not (member-equal nil (identifier-chunks-from before after ver)))
    :induct t))

;;;;;;;;;;;;;;;;;;;;

(define identifier-chunks ((cps code-point-listp) (ver versionp))
  :returns (chunks code-point-list-listp)
  :short "The chunks of a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the list of the pieces into which
     the identifier word boundaries cut the list
     [UTS #55, Section 5.1.2.1]:
     see @(see identifier-word-boundaries).
     No chunk is empty,
     and the chunks put together are the list.
     The function is meant for an identifier
     but is defined for every list of code points."))
  (identifier-chunks-from nil cps ver)
  :hooks (:fix)

  ///

  (defrule consp-of-identifier-chunks
    (equal (consp (identifier-chunks cps ver))
           (consp cps)))

  (defrule flatten-of-identifier-chunks
    (equal (acl2::flatten (identifier-chunks cps ver))
           (code-point-list-fix cps)))

  (defrule not-member-equal-of-nil-and-identifier-chunks
    (not (member-equal nil (identifier-chunks cps ver)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection script-extensions-of-titlecase-letter
  :short "The @('Script_Extensions') of a titlecase letter
          is the set of its one @('Script')."
  :long
  (xdoc::topstring
   (xdoc::p
    "So it does not matter by which of the two properties
     the Greek titlecase letters are recognized
     in the rules for identifier word boundaries.
     We prove this by checking each titlecase letter, for each version;
     there are thirty-one of them."))

  (local
   (define titlecase-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (equal (code-point-script-extensions cp ver)
            (list (code-point-script cp ver)))
     :hooks nil))

  (local
   (std::deflist titlecase-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (titlecase-ok x ver)))

  (defrulel titlecase-ok-listp-of-titlecase-letters
    (titlecase-ok-listp (range-list-code-points
                         (general-category-ranges
                          (general-category-titlecase-letter)
                          (version-fix ver)))
                        (version-fix ver))
    :rule-classes nil
    :enable version-fix-in-terms-of-version-case)

  (defrule script-extensions-of-titlecase-letter
    (implies (equal (general-category-kind
                     (code-point-general-category cp ver))
                    :titlecase-letter)
             (equal (code-point-script-extensions cp ver)
                    (list (code-point-script cp ver))))
    :use (titlecase-ok-listp-of-titlecase-letters
          (:instance titlecase-ok-when-member-equal-of-titlecase-ok-listp
                     (acl2::a (code-point-fix cp))
                     (x (range-list-code-points
                         (general-category-ranges
                          (general-category-titlecase-letter)
                          (version-fix ver))))
                     (ver (version-fix ver)))
          (:instance general-category-fix-when-titlecase-letter
                     (x (code-point-general-category cp ver))))
    :enable (titlecase-ok
             code-point-in-general-category-ranges)
    :disable (titlecase-ok-when-member-equal-of-titlecase-ok-listp
              general-category-fix-when-titlecase-letter)))
