; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-class")
(include-book "bidi-brackets")
(include-book "right-to-left-free")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-rule
  :parents (bidirectional-algorithm)
  :short "The Bidi Rule for the labels of domain names,
          and two rules derived from it."
  :long
  (xdoc::topstring
   (xdoc::p
    "A domain name is made of labels, the parts between its dots.
     The Bidi Rule ("
    (xdoc::ahref "https://www.rfc-editor.org/rfc/rfc5893" "RFC 5893")
    ", Section 2) is a condition on a label
     of a domain name that has right-to-left characters;
     `Bidi' is short for `bidirectional'.
     The rule is part of the 2008 revision
     of Internationalized Domain Names for Applications (IDNA2008),
     and Unicode IDNA Compatibility Processing ("
    (xdoc::ahref "https://www.unicode.org/reports/tr46/" "UTS #46")
    ", Section 4.1) applies it
     when its option @('CheckBidi') is on.
     The rule looks only at the @('Bidi_Class') of the characters,
     so the predicates of this book can be used
     without the Unicode Bidirectional Algorithm [UAX #9].
     A label is here a list of code points.")
   (xdoc::p
    "The rule is meant to give labels two properties
     when the algorithm displays them [RFC 5893, Section 3].
     Two different labels are not displayed alike
     in the same paragraph (label uniqueness),
     and the characters of a label stay together,
     between the characters that delimit it (character grouping).
     For the second property,
     this library has conditions on any text cut into segments,
     with proofs: see @(see bidi-confinement).
     This book is about the first property.")
   (xdoc::p
    "It has three predicates on a label.
     They differ in where they come from
     and in what is known about them.")
   (xdoc::ul
    (xdoc::li
     "@(tsee bidi-rule-p) is the Bidi Rule as [RFC 5893] states it,
      and @(tsee bidi-rule-domain-name-p)
      applies it to a domain name as [UTS #46] does.
      The rule alone does not make labels unique.
      It allows the characters of class @('ET')
      (@('European_Terminator')), such as the percent sign,
      and a terminator next to a European number
      becomes a part of the number,
      on whichever side of the number it stands
      [UAX #9, rule W5].
      The two labels U+05D0, @('1'), @('-'), @('%'), @('1')
      and U+05D0, @('%'), @('1'), @('-'), @('1'),
      where U+05D0 is the Hebrew letter alef,
      satisfy the rule and are displayed alike,
      in a paragraph of either direction.
      The rule also allows the characters of class @('BN')
      (@('Boundary_Neutral')),
      such as U+200C ZERO WIDTH NON-JOINER.
      The algorithm sets those aside,
      and afterwards each is placed with the character before it
      [UAX #9, rule X9 and Section 5.2].
      The two labels U+05D0, @('1'), U+200C, U+05D0
      and U+05D0, U+200C, @('1'), U+05D0
      satisfy the rule and are displayed alike.")
    (xdoc::li
     "@(tsee bidi-rule-strict-p) is the rule
      with the characters of those two classes excluded.
      It is not a published rule.
      It is close to what IDNA2008 has in effect for terminators:
      the characters that IDNA2008 permits in a label
      are listed in another document [RFC 5892],
      which this library does not model,
      and that list has few symbols and punctuation marks,
      while [UTS #46] accepts many.
      No two labels that satisfy this predicate are displayed alike,
      whatever the directions of the paragraphs that they are in.
      That is proved
      (see @(see bidi-rule-display-strict-theorem));
      the searches described below found none before the proof.")
    (xdoc::li
     "@(tsee bidi-rule-wide-p) is a rule of this library,
      not of a specification.
      It is for names that are not labels of domain names,
      which often begin or end with punctuation
      or have a currency sign in them.
      It lets punctuation stand at the two ends of a name,
      where the Bidi Rule wants a letter or a digit,
      and it lets a terminator stand anywhere
      but next to a European digit.
      It is for a paragraph from left to right only.
      No two names that satisfy this predicate
      are displayed alike in such a paragraph.
      That is proved:
      a function that does not go through the rules of the algorithm
      gives the display of such a name;
      it is proved to give different displays
      to different names (see @(see bidi-rule-display)),
      and the algorithm is proved to display the name
      as the function says (see @(see bidi-rule-display-theorem))."))
   (xdoc::p
    "A label that satisfies @(tsee bidi-rule-strict-p)
     satisfies @(tsee bidi-rule-wide-p):
     see @(see bidi-rule-theorems).
     So the wide rule extends the strict one,
     and the theorem for the wide rule,
     in a paragraph from left to right, is a theorem for both.
     The strict rule has a theorem of its own
     for the other directions of the paragraph.")
   (xdoc::p
    "For how the proofs go, see @(see bidi-rule-proof-plan).")
   (xdoc::p
    "The searches are tests of this library,
     in the file @('tests/bidi-rule.lisp').
     Each one takes a small set of characters,
     with one or two characters
     of each class that the predicate allows,
     among them paired brackets, a mirrored character
     and a nonspacing mark;
     it runs the algorithm on every list of those characters
     up to a length, and compares the displays
     of the lists that satisfy the predicate.
     The file says which characters and which lengths.")
   (xdoc::p
    "The terms `right-to-left label', `left-to-right label'
     and `Bidi domain name' are those of [RFC 5893, Section 1.4]:
     see @(tsee bidi-right-to-left-label-p)
     and @(tsee bidi-domain-name-p).
     In the names of the functions and in their documentation,
     the classes have the short names of [UAX #9, Table 4]:
     @('L') (@('Left_To_Right')),
     @('R') (@('Right_To_Left')),
     @('AL') (@('Arabic_Letter')),
     @('EN') (@('European_Number')),
     @('ES') (@('European_Separator')),
     @('ET') (@('European_Terminator')),
     @('AN') (@('Arabic_Number')),
     @('CS') (@('Common_Separator')),
     @('NSM') (@('Nonspacing_Mark')),
     @('BN') (@('Boundary_Neutral'))
     and @('ON') (@('Other_Neutral'))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-class-kind-present-p ((kind keywordp)
                                   (cps code-point-listp)
                                   (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points has a code point
          of a given bidirectional class,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The class is given by its kind,
     which is a keyword such as @(':european-number'):
     see @(tsee bidi-class)."))
  (and (consp cps)
       (or (equal (bidi-class-kind (code-point-bidi-class (car cps) ver))
                  kind)
           (bidi-class-kind-present-p kind (cdr cps) ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-class-kind-present-p
    :args ((cps code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (bidi-class-kind-present-p kind cps ver)
             :expand ((bidi-class-kind-present-p kind cps ver)
                      (bidi-class-kind-present-p kind
                                                 (code-point-list-fix cps)
                                                 ver)
                      (bidi-class-kind-present-p kind
                                                 cps
                                                 (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-right-to-left-label-p ((label code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a label is a right-to-left label,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A right-to-left label (`RTL label') is one
     that has a character of class @('R'), @('AL') or @('AN'),
     and any other label is a left-to-right label (`LTR label')
     [RFC 5893, Section 1.4].")
   (xdoc::p
    "This is not the predicate @(tsee right-to-left-free-p) negated:
     that one also looks for the three explicit formatting characters
     that start an embedding, an override or an isolate
     from right to left.
     A label that satisfies @(tsee bidi-rule-p) has none of the three,
     so for such a label the two agree:
     see @(see bidi-rule-theorems)."))
  (or (bidi-class-kind-present-p :right-to-left label ver)
      (bidi-class-kind-present-p :arabic-letter label ver)
      (bidi-class-kind-present-p :arabic-number label ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-domain-name-p ((labels code-point-list-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a domain name, given as the list of its labels,
          is a Bidi domain name,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Bidi domain name is one that has a right-to-left label
     [RFC 5893, Section 1.4],
     that is, one that has a character
     of class @('R'), @('AL') or @('AN') [UTS #46, Section 2]:
     see @(tsee bidi-right-to-left-label-p)."))
  (and (consp labels)
       (or (bidi-right-to-left-label-p (car labels) ver)
           (bidi-domain-name-p (cdr labels) ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-domain-name-p
    :hints (("Goal"
             :induct (bidi-domain-name-p labels ver)
             :expand ((bidi-domain-name-p labels ver)
                      (bidi-domain-name-p (code-point-list-list-fix labels)
                                          ver)
                      (bidi-domain-name-p labels (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-mark-code-point-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is of class @('NSM'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "@('NSM') is short for @('Nonspacing_Mark').
     This is a value of the @('Bidi_Class') property;
     most characters that have it are combining marks.
     In the Unicode Bidirectional Algorithm
     such a character takes the class of the character before it
     [UAX #9, rule W1]."))
  (equal (bidi-class-kind (code-point-bidi-class cp ver))
         :nonspacing-mark)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-marks-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that every code point of a list is of class @('NSM'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-mark-code-point-p)."))
  (bidi-mark-code-point-p x ver)
  ///
  (fty::deffixequiv bidi-marks-p
    :args ((x code-point-listp) (ver versionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-right-to-left-code-point-p ((cp code-point-p)
                                              (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the Bidi Rule allows a code point
          in a right-to-left label,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classes allowed are
     @('R'), @('AL'), @('AN'), @('EN'), @('ES'), @('CS'), @('ET'),
     @('ON'), @('BN') and @('NSM')
     [RFC 5893, Section 2, condition 2]."))
  (b* ((class (code-point-bidi-class cp ver)))
    (bidi-class-case class
                     :right-to-left t
                     :arabic-letter t
                     :arabic-number t
                     :european-number t
                     :european-separator t
                     :common-separator t
                     :european-terminator t
                     :other-neutral t
                     :boundary-neutral t
                     :nonspacing-mark t
                     :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-rule-right-to-left-code-points-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that the Bidi Rule allows every code point of a list
          in a right-to-left label,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-rule-right-to-left-code-point-p)."))
  (bidi-rule-right-to-left-code-point-p x ver)
  ///
  (fty::deffixequiv bidi-rule-right-to-left-code-points-p
    :args ((x code-point-listp) (ver versionp))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-left-to-right-code-point-p ((cp code-point-p)
                                              (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the Bidi Rule allows a code point
          in a left-to-right label,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classes allowed are
     @('L'), @('EN'), @('ES'), @('CS'), @('ET'),
     @('ON'), @('BN') and @('NSM')
     [RFC 5893, Section 2, condition 5]."))
  (b* ((class (code-point-bidi-class cp ver)))
    (bidi-class-case class
                     :left-to-right t
                     :european-number t
                     :european-separator t
                     :common-separator t
                     :european-terminator t
                     :other-neutral t
                     :boundary-neutral t
                     :nonspacing-mark t
                     :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-rule-left-to-right-code-points-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that the Bidi Rule allows every code point of a list
          in a left-to-right label,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-rule-left-to-right-code-point-p)."))
  (bidi-rule-left-to-right-code-point-p x ver)
  ///
  (fty::deffixequiv bidi-rule-left-to-right-code-points-p
    :args ((x code-point-listp) (ver versionp))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-right-to-left-end-p ((label code-point-listp)
                                       (ver versionp))
  :returns (yes/no booleanp)
  :short "Check that a label ends as the Bidi Rule
          wants a right-to-left label to end,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The label must end with a character
     of class @('R'), @('AL'), @('EN') or @('AN'),
     which characters of class @('NSM') may follow
     [RFC 5893, Section 2, condition 3].
     That is, the last character that is not of class @('NSM')
     is of one of the four classes.")
   (xdoc::p
    "The definition goes along the label:
     either the rest of the label ends in that way,
     or the first character is of one of the four classes
     and the rest is only characters of class @('NSM')."))
  (b* (((when (endp label)) nil)
       ((when (bidi-rule-right-to-left-end-p (cdr label) ver)) t)
       (class (code-point-bidi-class (car label) ver)))
    (and (bidi-class-case class
                          :right-to-left t
                          :arabic-letter t
                          :european-number t
                          :arabic-number t
                          :otherwise nil)
         (bidi-marks-p (cdr label) ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-rule-right-to-left-end-p
    :hints (("Goal"
             :induct (bidi-rule-right-to-left-end-p label ver)
             :expand ((bidi-rule-right-to-left-end-p label ver)
                      (bidi-rule-right-to-left-end-p
                       (code-point-list-fix label)
                       ver)
                      (bidi-rule-right-to-left-end-p label
                                                     (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-left-to-right-end-p ((label code-point-listp)
                                       (ver versionp))
  :returns (yes/no booleanp)
  :short "Check that a label ends as the Bidi Rule
          wants a left-to-right label to end,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The label must end with a character of class @('L') or @('EN'),
     which characters of class @('NSM') may follow
     [RFC 5893, Section 2, condition 6].
     The definition goes along the label
     like that of @(tsee bidi-rule-right-to-left-end-p)."))
  (b* (((when (endp label)) nil)
       ((when (bidi-rule-left-to-right-end-p (cdr label) ver)) t)
       (class (code-point-bidi-class (car label) ver)))
    (and (bidi-class-case class
                          :left-to-right t
                          :european-number t
                          :otherwise nil)
         (bidi-marks-p (cdr label) ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-rule-left-to-right-end-p
    :hints (("Goal"
             :induct (bidi-rule-left-to-right-end-p label ver)
             :expand ((bidi-rule-left-to-right-end-p label ver)
                      (bidi-rule-left-to-right-end-p
                       (code-point-list-fix label)
                       ver)
                      (bidi-rule-left-to-right-end-p label
                                                     (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-p ((label code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a label satisfies the Bidi Rule,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule has six conditions [RFC 5893, Section 2]:")
   (xdoc::ol
    (xdoc::li
     "The first character is of class @('L'), @('R') or @('AL').
      If it is of class @('R') or @('AL'),
      the label is a right-to-left label;
      if it is of class @('L'), it is a left-to-right label.")
    (xdoc::li
     "A right-to-left label has only characters of the classes
      @('R'), @('AL'), @('AN'), @('EN'), @('ES'), @('CS'), @('ET'),
      @('ON'), @('BN') and @('NSM'):
      see @(tsee bidi-rule-right-to-left-code-point-p).")
    (xdoc::li
     "A right-to-left label ends with a character
      of class @('R'), @('AL'), @('EN') or @('AN'),
      which characters of class @('NSM') may follow:
      see @(tsee bidi-rule-right-to-left-end-p).")
    (xdoc::li
     "A right-to-left label does not have
      both a character of class @('EN') and one of class @('AN').")
    (xdoc::li
     "A left-to-right label has only characters of the classes
      @('L'), @('EN'), @('ES'), @('CS'), @('ET'),
      @('ON'), @('BN') and @('NSM'):
      see @(tsee bidi-rule-left-to-right-code-point-p).")
    (xdoc::li
     "A left-to-right label ends with a character
      of class @('L') or @('EN'),
      which characters of class @('NSM') may follow:
      see @(tsee bidi-rule-left-to-right-end-p)."))
   (xdoc::p
    "So the empty label does not satisfy the rule:
     it has no first character.")
   (xdoc::p
    "The first condition says which labels
     are right-to-left labels in the other five,
     by the first character.
     The terminology of the same document says it
     by the characters of the whole label:
     see @(tsee bidi-right-to-left-label-p).
     For a label that satisfies the rule the two agree,
     which is a theorem of this library:
     see @(see bidi-rule-theorems).")
   (xdoc::p
    "The rule alone does not keep two labels
     from being displayed alike:
     see @(see bidi-rule) and @(tsee bidi-rule-strict-p)."))
  (b* (((unless (consp label)) nil)
       (first (code-point-bidi-class (car label) ver)))
    (bidi-class-case
     first
     :right-to-left
     (and (bidi-rule-right-to-left-code-points-p label ver)
          (bidi-rule-right-to-left-end-p label ver)
          (not (and (bidi-class-kind-present-p :european-number label ver)
                    (bidi-class-kind-present-p :arabic-number label ver))))
     :arabic-letter
     (and (bidi-rule-right-to-left-code-points-p label ver)
          (bidi-rule-right-to-left-end-p label ver)
          (not (and (bidi-class-kind-present-p :european-number label ver)
                    (bidi-class-kind-present-p :arabic-number label ver))))
     :left-to-right
     (and (bidi-rule-left-to-right-code-points-p label ver)
          (bidi-rule-left-to-right-end-p label ver))
     :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-rule-labels-p (x ver)
  :guard (and (code-point-list-listp x)
              (versionp ver))
  :short "Check that every label of a list satisfies the Bidi Rule,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-rule-p)."))
  (bidi-rule-p x ver)
  ///
  (fty::deffixequiv bidi-rule-labels-p
    :args ((x code-point-list-listp) (ver versionp))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-domain-name-p ((labels code-point-list-listp)
                                 (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a domain name, given as the list of its labels,
          passes the check of the Bidi Rule,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The rule applies to the labels of Bidi domain names
     [RFC 5893, Section 2]:
     if the domain name is a Bidi domain name,
     each of its labels must satisfy the rule
     [UTS #46, Section 4.1];
     see @(tsee bidi-domain-name-p) and @(tsee bidi-rule-p).
     A domain name that is not a Bidi domain name
     passes the check whatever its labels are.")
   (xdoc::p
    "This is only the check that goes with the option @('CheckBidi').
     The other validity criteria of [UTS #46],
     and its mapping of the characters, are not modeled."))
  (or (not (bidi-domain-name-p labels ver))
      (bidi-rule-labels-p labels ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-strict-p ((label code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a label satisfies the Bidi Rule
          and has no character of class @('ET') or @('BN'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This predicate is of this library: it is not in [RFC 5893].
     It adds two conditions to @(tsee bidi-rule-p),
     each of which takes away a way in which two labels
     that satisfy the rule are displayed alike:")
   (xdoc::ul
    (xdoc::li
     "No character of class @('ET') (@('European_Terminator')).
      A terminator next to a European number
      becomes a part of the number,
      whether it comes before the number or after it
      [UAX #9, rule W5].
      So, with U+05D0 for the Hebrew letter alef,
      the label U+05D0, @('1'), @('-'), @('%'), @('1')
      has the two numbers @('1') and @('%1'),
      the label U+05D0, @('%'), @('1'), @('-'), @('1')
      has the one number @('%1-1'),
      and both are displayed as
      @('%'), @('1'), @('-'), @('1'), U+05D0.")
    (xdoc::li
     "No character of class @('BN') (@('Boundary_Neutral')).
      The algorithm sets such a character aside [UAX #9, rule X9],
      and when it is kept for the display
      it takes the level of the character before it
      [UAX #9, Section 5.2].
      So the label U+05D0, @('1'), U+200C, U+05D0,
      where the third character goes with the digit,
      and the label U+05D0, U+200C, @('1'), U+05D0,
      where the second character goes with the letter,
      are both displayed as U+05D0, @('1'), U+200C, U+05D0."))
   (xdoc::p
    "No two labels that satisfy this predicate are displayed alike.
     The paragraph of each label can go from left to right
     or from right to left,
     or take its direction from the first strong character of the label,
     and the two labels need not be in paragraphs of the same direction.
     That is the theorem
     @('bidi-display-is-one-to-one-when-bidi-rule-strict-p')
     (see @(see bidi-rule-display-strict-theorem)).
     A label that satisfies this predicate
     is displayed in the same way in all those paragraphs.")
   (xdoc::p
    "A search checks this on short labels:
     of all the lists of one to six characters taken from thirteen,
     416,724 lists of six characters and 40,017 shorter ones
     are right-to-left labels that satisfy it,
     and no two of them are displayed alike,
     in a paragraph from left to right
     or in a paragraph from right to left.
     The thirteen characters are
     two Hebrew letters (class @('R')), an Arabic letter (@('AL')),
     two European digits (@('EN')), two Arabic-Indic digits (@('AN')),
     the hyphen (@('ES')), the comma (@('CS')),
     the asterisk and the two parentheses (@('ON')),
     and a Hebrew point (@('NSM')).
     The tests of the library run the search up to five characters,
     and it was run once for six.")
   (xdoc::p
    "A left-to-right label that satisfies the rule
     has no right-to-left character,
     and is displayed as it is stored in a paragraph from left to right:
     see @(see bidi-rule-theorems).
     In a paragraph from right to left
     each of its characters gets level 2,
     and it is again displayed as it is stored:
     see @(see bidi-rule-left-to-right-label).
     A second search has two letters of class @('L') in its set
     of eleven characters,
     and compares the labels of the two kinds together:
     85,486 labels of six characters and 12,264 shorter ones,
     none displayed like another in either direction."))
  (and (bidi-rule-p label ver)
       (not (bidi-class-kind-present-p :european-terminator label ver))
       (not (bidi-class-kind-present-p :boundary-neutral label ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-wide-code-point-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if the wide rule allows a code point in a name,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The classes allowed are
     @('L'), @('R'), @('AL'), @('AN'), @('EN'), @('ES'), @('CS'),
     @('ET'), @('ON') and @('NSM'):
     those that the Bidi Rule allows in a label of either direction
     [RFC 5893, Section 2, conditions 2 and 5],
     without @('BN').
     So a name has no white space
     and no formatting character.
     See @(tsee bidi-rule-wide-p)."))
  (b* ((class (code-point-bidi-class cp ver)))
    (bidi-class-case class
                     :left-to-right t
                     :right-to-left t
                     :arabic-letter t
                     :arabic-number t
                     :european-number t
                     :european-separator t
                     :common-separator t
                     :european-terminator t
                     :other-neutral t
                     :nonspacing-mark t
                     :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist bidi-rule-wide-code-points-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that the wide rule allows every code point of a list,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-rule-wide-code-point-p)."))
  (bidi-rule-wide-code-point-p x ver)
  ///
  (fty::deffixequiv bidi-rule-wide-code-points-p
    :args ((x code-point-listp) (ver versionp))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-wide-start-p ((name code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check that neither a digit nor a paired bracket
          comes before the first right-to-left letter of a name,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "A right-to-left letter is a character of class @('R') or @('AL'),
     a digit is one of class @('EN') or @('AN'),
     and a paired bracket is a character
     whose @('Bidi_Paired_Bracket_Type') is not @('None'):
     see @(tsee code-point-bidi-bracket).
     A name with a digit and no right-to-left letter
     does not pass the check.")
   (xdoc::p
    "The two conditions are for a right-to-left name
     in a paragraph from left to right.
     A digit before the first letter is displayed at the left end,
     where a digit after the last letter is also displayed:
     alef, @('1') and @('1'), alef are both displayed as @('1'), alef.
     A bracket before the first letter
     can form a pair that takes the direction of the paragraph
     [UAX #9, rule N0],
     while the same bracket further on is displayed as its mirror image
     [UAX #9, rule L4]:
     @('('), alef, @('('), alef and @('('), alef, @(')'), alef
     are both displayed as @('('), alef, @(')'), alef."))
  (b* (((when (endp name)) t)
       (cp (code-point-fix (car name)))
       (class (code-point-bidi-class cp ver)))
    (bidi-class-case
     class
     :right-to-left t
     :arabic-letter t
     :european-number nil
     :arabic-number nil
     :otherwise (and (not (code-point-bidi-bracket cp ver))
                     (bidi-rule-wide-start-p (cdr name) ver))))
  :hooks nil

  ///

  (fty::deffixequiv bidi-rule-wide-start-p
    :hints (("Goal"
             :induct (bidi-rule-wide-start-p name ver)
             :expand ((bidi-rule-wide-start-p name ver)
                      (bidi-rule-wide-start-p (code-point-list-fix name) ver)
                      (bidi-rule-wide-start-p name (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-drop-marks ((cps code-point-listp) (ver versionp))
  :returns (rest code-point-listp)
  :short "Remove the code points of class @('NSM')
          from a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-mark-code-point-p)."))
  (b* (((when (endp cps)) nil)
       (cp (code-point-fix (car cps)))
       ((when (bidi-mark-code-point-p cp ver))
        (bidi-drop-marks (cdr cps) ver)))
    (cons cp (bidi-drop-marks (cdr cps) ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-drop-marks
    :hints (("Goal"
             :induct (bidi-drop-marks cps ver)
             :expand ((bidi-drop-marks cps ver)
                      (bidi-drop-marks (code-point-list-fix cps) ver)
                      (bidi-drop-marks cps (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-terminator-next-to-digit-p ((cps code-point-listp)
                                         (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a list of code points has a code point of class @('ET')
          next to one of class @('EN'),
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, a European terminator directly before a European digit
     or directly after one."))
  (b* (((when (or (endp cps) (endp (cdr cps)))) nil)
       (kind1 (bidi-class-kind (code-point-bidi-class (car cps) ver)))
       (kind2 (bidi-class-kind (code-point-bidi-class (cadr cps) ver))))
    (or (and (equal kind1 :european-terminator)
             (equal kind2 :european-number))
        (and (equal kind1 :european-number)
             (equal kind2 :european-terminator))
        (bidi-terminator-next-to-digit-p (cdr cps) ver)))
  :hooks nil

  ///

  (fty::deffixequiv bidi-terminator-next-to-digit-p
    :hints (("Goal"
             :induct (bidi-terminator-next-to-digit-p cps ver)
             :expand ((bidi-terminator-next-to-digit-p cps ver)
                      (bidi-terminator-next-to-digit-p
                       (code-point-list-fix cps)
                       ver)
                      (bidi-terminator-next-to-digit-p cps
                                                       (version-fix ver)))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-rule-wide-p ((name code-point-listp) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a name satisfies the wide rule,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "This rule is of this library: it is not in a specification.
     It is for names that are displayed in a paragraph from left to right
     and that are not labels of domain names,
     so that they may begin or end with punctuation.
     A name is a list of code points.
     The conditions are these:")
   (xdoc::ol
    (xdoc::li
     "The name has only characters of the classes
      @('L'), @('R'), @('AL'), @('AN'), @('EN'), @('ES'), @('CS'),
      @('ET'), @('ON') and @('NSM'):
      see @(tsee bidi-rule-wide-code-point-p).")
    (xdoc::li
     "If the name has a character of class @('R'), @('AL') or @('AN'),
      that is, if it is a right-to-left name
      (see @(tsee bidi-right-to-left-label-p)),
      then:"
     (xdoc::ol
      (xdoc::li
       "It has no character of class @('L').")
      (xdoc::li
       "It does not have both a character of class @('EN')
        and one of class @('AN').")
      (xdoc::li
       "Neither a digit nor a paired bracket
        comes before its first right-to-left letter:
        see @(tsee bidi-rule-wide-start-p).")
      (xdoc::li
       "No character of class @('ET') stands next to one of class @('EN'),
        when the characters of class @('NSM') are left out:
        see @(tsee bidi-drop-marks)
        and @(tsee bidi-terminator-next-to-digit-p)."))))
   (xdoc::p
    "A left-to-right name has only the first condition.
     It is displayed as it is stored:
     see @(see bidi-rule-theorems).")
   (xdoc::p
    "Compared with the Bidi Rule [RFC 5893, Section 2],
     a right-to-left name need not begin with a letter
     and need not end with a letter or a digit,
     and a left-to-right name can begin and end with any character
     that the first condition allows.
     In return the name has no character of class @('BN'),
     and a terminator is kept away from the European digits:
     see @(tsee bidi-rule-strict-p) for what goes wrong otherwise.
     The characters of class @('NSM') are left out in that condition
     because such a character takes the class
     of the character before it [UAX #9, rule W1]:
     after a digit it is a part of the number,
     and after a terminator it is a terminator.")
   (xdoc::p
    "What is known about this rule is a search:
     of all the lists of one to six characters taken from sixteen,
     4,437,669 lists of six characters and 318,375 shorter ones
     are right-to-left names that satisfy it,
     and no two of them are displayed alike
     in a paragraph from left to right.
     The sixteen characters are the thirteen
     of the search of @(tsee bidi-rule-strict-p),
     the percent sign (class @('ET')),
     and the less-than and greater-than signs,
     which are of class @('ON') and are displayed as their mirror images
     at a right-to-left level, but are not paired brackets.
     The tests of the library run the search up to five characters,
     and it was run once for six.
     A second search, over twelve characters
     with two letters of class @('L'),
     compares the names of the two kinds together:
     816,451 names of six characters and 101,423 shorter ones,
     none displayed like another.
     For each condition of the second group,
     the tests also have two names that are displayed alike
     and that the condition keeps apart:
     one of them fails that condition and no other.")
   (xdoc::p
    "The rule does not hold for a paragraph from right to left.
     There a Hebrew point followed by alef
     and alef followed by the point are displayed alike,
     and both satisfy the rule.
     The first of the two does not satisfy @(tsee bidi-rule-strict-p),
     which holds for paragraphs of any direction.")
   (xdoc::p
    "That no two names of any length that satisfy this rule
     are displayed alike, in a paragraph from left to right,
     is proved: see @(see bidi-rule-display-theorem)."))
  (and (bidi-rule-wide-code-points-p name ver)
       (or (not (bidi-right-to-left-label-p name ver))
           (and (not (bidi-class-kind-present-p :left-to-right name ver))
                (not (and (bidi-class-kind-present-p :european-number
                                                     name
                                                     ver)
                          (bidi-class-kind-present-p :arabic-number
                                                     name
                                                     ver)))
                (bidi-rule-wide-start-p name ver)
                (not (bidi-terminator-next-to-digit-p
                      (bidi-drop-marks name ver)
                      ver)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Lemmas for the theorems below: what the classes that a predicate allows
; say about the classes that are present in a list.

(defrulel not-present-when-left-to-right-code-points
  (implies (and (bidi-rule-left-to-right-code-points-p x ver)
                (member-equal kind '(:right-to-left
                                     :arabic-letter
                                     :arabic-number)))
           (not (bidi-class-kind-present-p kind x ver)))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-rule-left-to-right-code-point-p))

(defrulel not-present-when-right-to-left-code-points
  (implies (bidi-rule-right-to-left-code-points-p x ver)
           (not (bidi-class-kind-present-p :left-to-right x ver)))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-rule-right-to-left-code-point-p))

(defrulel right-to-left-free-p-when-left-to-right-code-points
  (implies (bidi-rule-left-to-right-code-points-p x ver)
           (right-to-left-free-p x ver))
  :induct (len x)
  :enable (len
           bidi-rule-left-to-right-code-point-p
           right-to-left-code-point-p))

(defrulel right-to-left-free-p-when-wide-code-points
  (implies (and (bidi-rule-wide-code-points-p x ver)
                (not (bidi-class-kind-present-p :right-to-left x ver))
                (not (bidi-class-kind-present-p :arabic-letter x ver))
                (not (bidi-class-kind-present-p :arabic-number x ver)))
           (right-to-left-free-p x ver))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-rule-wide-code-point-p
           right-to-left-code-point-p))

(defrulel wide-code-points-when-right-to-left-code-points
  (implies (and (bidi-rule-right-to-left-code-points-p x ver)
                (not (bidi-class-kind-present-p :european-terminator x ver))
                (not (bidi-class-kind-present-p :boundary-neutral x ver)))
           (bidi-rule-wide-code-points-p x ver))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-rule-right-to-left-code-point-p
           bidi-rule-wide-code-point-p))

(defrulel wide-code-points-when-left-to-right-code-points
  (implies (and (bidi-rule-left-to-right-code-points-p x ver)
                (not (bidi-class-kind-present-p :european-terminator x ver))
                (not (bidi-class-kind-present-p :boundary-neutral x ver)))
           (bidi-rule-wide-code-points-p x ver))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-rule-left-to-right-code-point-p
           bidi-rule-wide-code-point-p))

(defrulel not-present-in-bidi-drop-marks-when-not-present
  (implies (not (bidi-class-kind-present-p kind x ver))
           (not (bidi-class-kind-present-p kind (bidi-drop-marks x ver) ver)))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-drop-marks))

(defrulel not-bidi-terminator-next-to-digit-p-when-no-terminator
  (implies (not (bidi-class-kind-present-p :european-terminator x ver))
           (not (bidi-terminator-next-to-digit-p x ver)))
  :induct (len x)
  :enable (len
           bidi-class-kind-present-p
           bidi-terminator-next-to-digit-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-theorems
  :short "Theorems about the Bidi Rule
          and about the two rules derived from it."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first theorem is about the two ways
     in which [RFC 5893] says what a right-to-left label is:
     by the first character, in the first condition of the rule,
     and by the characters of the whole label, in the terminology.
     For a label that satisfies the rule they agree:
     the label has a character of class @('R'), @('AL') or @('AN')
     exactly when its first character is not of class @('L'),
     that is, when it is of class @('R') or @('AL').")
   (xdoc::p
    "The next two theorems are about left-to-right labels and names.
     One that satisfies @(tsee bidi-rule-p),
     or one that satisfies @(tsee bidi-rule-wide-p),
     has no character that can make text
     be displayed from right to left:
     see @(tsee right-to-left-free-p).
     So, in a paragraph that is not set from right to left,
     the Unicode Bidirectional Algorithm displays it as it is stored;
     that is the theorem @('bidi-display-when-right-to-left-free-p')
     of @(see bidi-left-to-right).
     Two different left-to-right labels are then not displayed alike.
     A left-to-right label that satisfies @(tsee bidi-rule-strict-p)
     is displayed as it is stored
     in a paragraph from right to left too
     (see @(see bidi-rule-left-to-right-label)).")
   (xdoc::p
    "The last theorem says that the wide rule extends the strict one:
     a label that satisfies @(tsee bidi-rule-strict-p)
     satisfies @(tsee bidi-rule-wide-p)."))

  (defrule bidi-right-to-left-label-p-when-bidi-rule-p
    (implies (bidi-rule-p label ver)
             (equal (bidi-right-to-left-label-p label ver)
                    (not (equal (bidi-class-kind
                                 (code-point-bidi-class (car label) ver))
                                :left-to-right))))
    :enable (bidi-rule-p
             bidi-right-to-left-label-p)
    :expand ((bidi-class-kind-present-p :right-to-left label ver)
             (bidi-class-kind-present-p :arabic-letter label ver)))

  (defruled right-to-left-free-p-when-bidi-rule-p
    (implies (and (bidi-rule-p label ver)
                  (not (bidi-right-to-left-label-p label ver)))
             (right-to-left-free-p label ver))
    :enable (bidi-rule-p
             bidi-right-to-left-label-p)
    :expand ((bidi-class-kind-present-p :right-to-left label ver)
             (bidi-class-kind-present-p :arabic-letter label ver)))

  (defruled right-to-left-free-p-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name ver)
                  (not (bidi-right-to-left-label-p name ver)))
             (right-to-left-free-p name ver))
    :enable (bidi-rule-wide-p
             bidi-right-to-left-label-p))

  (defrule bidi-rule-wide-p-when-bidi-rule-strict-p
    (implies (bidi-rule-strict-p label ver)
             (bidi-rule-wide-p label ver))
    :enable (bidi-rule-strict-p
             bidi-rule-wide-p
             bidi-rule-p
             bidi-right-to-left-label-p)
    :expand (bidi-rule-wide-start-p label ver)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc bidi-rule-proof-plan
  :short "How it is proved that no two names that satisfy the wide rule
          are displayed alike in a paragraph from left to right,
          and that no two labels that satisfy the strict rule
          are displayed alike in paragraphs of any direction."
  :long
  (xdoc::topstring
   (xdoc::p
    "The four steps below are proved.
     The first three are for @(tsee bidi-rule-wide-p)
     in a paragraph from left to right.
     The fourth is for @(tsee bidi-rule-strict-p)
     in a paragraph of another direction.
     The topic kept its name from the time
     when it was the plan of the proofs.")
   (xdoc::h3 "The statements")
   (xdoc::p
    "For the wide rule, in a paragraph from left to right:")
   (xdoc::codeblock
    "(implies (and (bidi-rule-wide-p x ver)"
    "              (bidi-rule-wide-p y ver)"
    "              (equal (paragraph-direction-kind direction)"
    "                     :left-to-right)"
    "              (equal (bidi-display x direction ver)"
    "                     (bidi-display y direction ver)))"
    "         (equal (code-point-list-fix x)"
    "                (code-point-list-fix y)))")
   (xdoc::p
    "This is the theorem
     @('bidi-display-is-one-to-one-when-bidi-rule-wide-p')
     (see @(see bidi-rule-display-theorem)).
     Since a label that satisfies the strict rule satisfies the wide rule
     (see @(see bidi-rule-theorems)),
     it is also a theorem about the strict rule in such a paragraph.
     For the strict rule, in paragraphs of any direction:")
   (xdoc::codeblock
    "(implies (and (bidi-rule-strict-p x ver)"
    "              (bidi-rule-strict-p y ver)"
    "              (equal (bidi-display x direction1 ver)"
    "                     (bidi-display y direction2 ver)))"
    "         (equal (code-point-list-fix x)"
    "                (code-point-list-fix y)))")
   (xdoc::p
    "This is the theorem
     @('bidi-display-is-one-to-one-when-bidi-rule-strict-p')
     (see @(see bidi-rule-display-strict-theorem)).
     Each of the two directions can be given in any of the three ways
     (see @(tsee paragraph-direction)):
     @(':left-to-right'), @(':right-to-left'), or @(':first-strong'),
     where the direction is taken from the label itself.
     The two labels can be in paragraphs of different directions.
     The wide rule has no such theorem
     for a paragraph from right to left:
     it does not hold there (see @(tsee bidi-rule-wide-p)).")
   (xdoc::p
    "Here @(tsee bidi-display) is the text as it is displayed,
     with every character kept and the mirrored ones replaced,
     and the name is a paragraph by itself.
     The theorems are in books that load the algorithm;
     the book of the rules does not.")
   (xdoc::h3 "The proof: read the name back from its display")
   (xdoc::p
    "A proof by cases on two names at once does not look practical.
     The proof has a function from a display to a name,
     and shows that it gives back every name that satisfies the rule
     from the display of that name.
     Two names with the same display are then the same name.
     A left-to-right name is displayed as it is stored
     (see @(see bidi-rule-theorems)),
     so the work is for the right-to-left names.
     It has three steps for the wide rule;
     a fourth is for the strict rule in the other directions.")
   (xdoc::p
    "An example:
     the name is @('*'), a Hebrew point, alef, @('1'), @(','), @('2'),
     @('-'), bet, @('-'), @('%').
     Its levels are 0, 0, 1, 2, 2, 2, 1, 1, 0, 0,
     and it is displayed as
     @('*'), the point, bet, @('-'), @('1'), @(','), @('2'), alef,
     @('-'), @('%').
     The two characters before the first letter and the two at the end
     stay where they are;
     the six in the middle are put in the opposite order,
     except that the number @('1,2') keeps its own order.")
   (xdoc::ol
    (xdoc::li
     "<b>The levels, computed without the rules of the algorithm.</b>
      The function @(tsee bidi-name-levels) gives the level
      that each character of a right-to-left name gets
      in a paragraph from left to right,
      by a recursion on the classes of the characters.
      Each mark goes with the character before it
      [UAX #9, rule W1].
      A number is a run of digits,
      and of single separators between two digits that rule W4 joins:
      a separator of class @('ES') (@('European_Separator'))
      or @('CS') (@('Common_Separator'))
      between two European digits,
      and one of class @('CS') between two Arabic digits,
      where a European digit that follows an Arabic letter
      counts as an Arabic digit [UAX #9, rule W2].
      The characters of a number get level 2.
      The other characters get level 0
      before the first right-to-left letter;
      level 1 from that letter to the last character that is a letter,
      a character of a number,
      a bracket of a pair with a letter or a digit inside,
      or a mark after such a bracket;
      and level 0 after that character.
      That the algorithm gives those levels is the theorem
      @('bidi-paragraph-all-levels-when-bidi-rule-wide-p')
      (see @(see bidi-rule-display-levels)).
      Its proof follows the algorithm rule by rule.
      The classes after the rules W1 to W7 are computed
      and proved first (see @(see bidi-rule-display-weak)).
      The delicate rule among those is W2:
      a European digit after an Arabic letter becomes an Arabic digit,
      and that changes which separators join two numbers,
      so alef, @('1'), @('-'), @('2') has one number
      and the same with an Arabic letter in place of alef has two.
      The delicate rule after them is N0, on the bracket pairs:
      it looks at what is inside a pair
      after it has changed the brackets of the pairs before it.
      The proof needed a fact about the pairs themselves,
      that no two of them cross,
      which is now the theorem
      @('bidi-pairs-nested-p-of-bidi-bracket-pairs').
      This is the largest step.")
    (xdoc::li
     "<b>The display, from those levels.</b>
      When the levels are only 0, 1 and 2,
      rule L2 puts a stretch of levels 1 and 2 in the opposite order
      and then puts each number back in its own order;
      rule L3 puts each mark after the character that it follows
      in the name;
      rule L4 replaces the mirrored characters of level 1.
      The function @(tsee bidi-name-display) computes that
      (see @(see bidi-rule-display)),
      and the theorem of @(see bidi-rule-display-order) says that,
      with the levels of the first step,
      @(tsee bidi-arrange-with-levels) and rule L4
      give what that function gives.
      The theorem about a clean cut
      (see @(see bidi-clean-cut-display))
      separates the parts of level 0 at the two ends.
      Rule L3 goes by the general category of a character,
      and the function by its class.
      The two agree on the characters
      that the wide rule allows in a right-to-left name:
      in the three versions, the characters of class @('NSM')
      (@('Nonspacing_Mark')) are combining marks,
      and the other combining marks
      are of class @('L') (@('Left_To_Right')).
      That is the theorem of @(see bidi-combining-mark-class).")
    (xdoc::li
     "<b>The way back.</b>
      The function @(tsee bidi-name-read) reads a name back
      from a display,
      and it is proved to give back every name
      that satisfies the wide rule
      from what @(tsee bidi-name-display) gives for it
      (see @(see bidi-rule-display-theorems)).
      The characters at the two ends that stayed in place
      are found by their classes:
      before the first letter of the name
      there is neither a digit nor a paired bracket,
      and after the stretch of levels 1 and 2 there is no letter.
      In the stretch between them the numbers are found,
      the order of the pieces is turned back,
      and the mirrored characters are replaced back.
      The proof uses two of the conditions of the rule:
      the one on the start of the name,
      and that the name does not have both kinds of digits.
      The tests have two names with both kinds of digits
      that are displayed alike:
      for those the function cannot tell which name it was.
      The other conditions are for the first two steps.")
    (xdoc::li
     "<b>The strict rule, in the other directions.</b>
      A right-to-left label that satisfies the strict rule
      begins with a letter,
      and only marks come after its last letter or digit.
      So the middle part of the first step is the whole label,
      and no character has level 0.
      In a paragraph from right to left,
      the classes after the rules W1 to W7 are the same
      as in a paragraph from left to right,
      because the label does not start with a mark;
      rule N0 again changes some brackets to the class @('R')
      (@('Right_To_Left')) and nothing else;
      rules N1 and N2 give @('R') to every neutral character that is left;
      and the levels are 1 and 2, the same as in the first step.
      That is the theorem
      @('bidi-paragraph-all-levels-at-level-1-when-bidi-rule-strict-p')
      (see @(see bidi-rule-display-strict-theorem)).
      It follows from a theorem about the wide rule,
      for a right-to-left name whose first character is not a mark
      (see @(see bidi-rule-display-levels)).
      With the same levels the display is the same, by the second step.
      A left-to-right label is displayed as it is stored
      in a paragraph from right to left too,
      but its levels are not 0 there.
      Its first character is of class @('L'),
      each digit takes the class of the letter before it
      [UAX #9, rule W7],
      every neutral character is then between two characters
      of class @('L') and takes that class [UAX #9, rule N1],
      and so every character gets level 2
      (see @(see bidi-rule-left-to-right-label)).
      A paragraph in which no level is odd is displayed as it is stored
      (see @(see bidi-display-even-levels-theorem)).
      When the direction is taken from the first strong character,
      the paragraph goes from right to left for a right-to-left label
      and from left to right for a left-to-right label.
      So a label that satisfies the strict rule
      has one display in all those paragraphs,
      the one that @(tsee bidi-name-display) gives,
      and the third step gives the label back from it."))
   (xdoc::h3 "Size, and what the theorems do not cover")
   (xdoc::p
    "The first two steps have five books and some 6,300 lines.
     The third is reasoning about lists, without the algorithm;
     its book has some 2,500 lines.
     The fourth added one book and some 1,700 lines.")
   (xdoc::p
    "The theorems hold for names of any length,
     in each of the three versions of Unicode that the library has.
     They are for a name that is a paragraph by itself.
     They say nothing about a name inside a longer text
     (for that, see @(see bidi-self-contained-segments)).
     For the wide rule they are for a paragraph from left to right only."))
  :parents (bidi-rule))
