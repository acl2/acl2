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

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ right-to-left-free
  :parents (bidirectional-algorithm)
  :short "Text that no character can make
          be displayed from right to left."
  :long
  (xdoc::topstring
   (xdoc::p
    "Most text has no character of a script written from right to left,
     and no formatting character that turns the direction around.
     The Unicode Bidirectional Algorithm [UAX #9]
     displays such a text in the order in which it is stored,
     unless the paragraph is set from right to left.
     This book has the predicate that says
     which code points such a text must not have,
     @(tsee right-to-left-code-point-p),
     and the predicate for a list, @(tsee right-to-left-free-p).
     They look only at the @('Bidi_Class') property,
     so that they can be used without the algorithm.
     The theorems that such a text is displayed in the stored order
     are in @(see bidi-left-to-right)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define right-to-left-code-point-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point can make text
          be displayed from right to left,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, check if its bidirectional class
     is one of the following six [UAX #9, Table 4]:")
   (xdoc::ul
    (xdoc::li
     "The two strong right-to-left classes,
      @('R') (@('Right_To_Left')) and @('AL') (@('Arabic_Letter')).")
    (xdoc::li
     "@('AN') (@('Arabic_Number')),
      the class of the Arabic-Indic digits
      and of a few other characters used in numbers.
      A number is displayed from left to right,
      but in a paragraph from left to right
      two numbers of this class with a space between them
      are displayed in the opposite order:
      for the characters between them,
      numbers act as right-to-left characters [UAX #9, rule N1].
      The European digits, of class @('EN'), do not do this
      in a text that has no character of the two strong classes above.")
    (xdoc::li
     "The three classes
      of the explicit directional formatting characters
      that start an embedding, an override or an isolate
      from right to left:
      @('RLE') (@('Right_To_Left_Embedding')),
      @('RLO') (@('Right_To_Left_Override'))
      and @('RLI') (@('Right_To_Left_Isolate')).")))
  (b* ((class (code-point-bidi-class cp ver)))
    (bidi-class-case class
                     :right-to-left t
                     :arabic-letter t
                     :arabic-number t
                     :right-to-left-embedding t
                     :right-to-left-override t
                     :right-to-left-isolate t
                     :otherwise nil))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(std::deflist right-to-left-free-p (x ver)
  :guard (and (code-point-listp x)
              (versionp ver))
  :short "Check that no code point of a list
          can make text be displayed from right to left,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee right-to-left-code-point-p).
     A text that satisfies this predicate,
     in a paragraph that is not set from right to left,
     is displayed in the order in which it is stored,
     by the Unicode Bidirectional Algorithm [UAX #9]:
     every character gets an even level,
     so nothing is reversed and nothing is drawn as its mirror image.
     Those are theorems of this library:
     see @(see bidi-left-to-right).")
   (xdoc::p
    "The specification of the skeleton states a weaker condition:
     that the bidirectional skeleton
     of a string with no character of class @('R') or @('AL'),
     for a paragraph from left to right,
     is its internal skeleton [UTS #39, Section 4].
     That condition is not enough,
     so we exclude four more classes.
     For each of the four there is a string
     with no character of class @('R') or @('AL')
     that is displayed in another order than the stored one,
     and whose bidirectional skeleton is not its internal skeleton:
     the Arabic-Indic digits U+0661 and U+0662 with a space between them
     are displayed with U+0662 first;
     after U+202E RIGHT-TO-LEFT OVERRIDE,
     the letters a, b are displayed as b, a;
     and after U+202B RIGHT-TO-LEFT EMBEDDING
     or U+2067 RIGHT-TO-LEFT ISOLATE,
     an exclamation mark and a question mark
     are displayed with the question mark first.
     These are among the tests of this library,
     in the file @('tests/properties.lisp')."))
  (right-to-left-code-point-p x ver)
  :negatedp t

  ///

  (fty::deffixequiv right-to-left-free-p
    :args ((x code-point-listp) (ver versionp))
    :hints (("Goal"
             :induct (right-to-left-free-p x ver)
             :in-theory (enable right-to-left-free-p)))))

;;;;;;;;;;;;;;;;;;;;

(defsection right-to-left-free-p-below-590
  :short "No code point below U+0590
          can make text be displayed from right to left."
  :long
  (xdoc::topstring
   (xdoc::p
    "U+0590 is the first code point of the Hebrew block.
     So a list of code points below it,
     such as a list of ASCII code points
     or of Latin, Greek and Cyrillic letters,
     satisfies the guard of @(tsee skeleton).
     We prove this by checking the code points below U+0590,
     for each version."))

  (local
   (define below-ok ((cp code-point-p) (ver versionp))
     :returns (yes/no booleanp)
     (or (>= (code-point-fix cp) #x590)
         (not (right-to-left-code-point-p cp ver)))
     :hooks nil))

  (local
   (std::deflist below-ok-listp (x ver)
     :guard (and (code-point-listp x)
                 (versionp ver))
     (below-ok x ver)))

  (defrulel below-ok-listp-of-all-code-points
    (below-ok-listp (all-code-points) (version-fix ver))
    :enable (version-fix-in-terms-of-version-case
             (:e all-code-points))
    :disable below-ok-listp-of-cons)

  (defrule not-right-to-left-code-point-p-when-below-590
    (implies (< (code-point-fix cp) #x590)
             (not (right-to-left-code-point-p cp ver)))
    :use (:instance below-ok-when-member-equal-of-below-ok-listp
                    (acl2::a (code-point-fix cp))
                    (x (all-code-points))
                    (ver (version-fix ver)))
    :enable below-ok)

  (defrule right-to-left-free-p-when-all-below-590
    (implies (code-points-below-p cps #x590)
             (right-to-left-free-p cps ver))
    :induct t
    :enable (code-points-below-p
             right-to-left-free-p)))
