; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-reordering")
(include-book "bidi-mirroring")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidirectional-algorithm
  :parents (unicode)
  :short "The Unicode Bidirectional Algorithm:
          the order in which text is displayed
          when it has characters of scripts written from right to left."
  :long
  (xdoc::topstring
   (xdoc::p
    "Text is stored in the order in which it is read and typed.
     Hebrew and Arabic are written from right to left,
     but numbers and words of other scripts inside them
     are written from left to right,
     so the order on the display is not the order in the store.
     The Unicode Bidirectional Algorithm [UAX #9],
     often called the UBA or the bidi algorithm,
     says what the order on the display is.
     It gives each character an embedding level, which is a number:
     text at an even level runs from left to right,
     and text at an odd level from right to left,
     and a higher level is text set inside text of the level below.
     The order of display follows from the levels.")
   (xdoc::p
    "This library has the rules of [UAX #9, Section 3]
     that give the levels and the order:")
   (xdoc::ul
    (xdoc::li
     "P1, which cuts the text into paragraphs,
      and P2 and P3, which find the direction of a paragraph
      when it is not given:
      see @(tsee bidi-paragraph-embedding-level)
      and @(see bidi-reordering).")
    (xdoc::li
     "X1 to X8, which follow the explicit formatting characters
      (embeddings, overrides and isolates):
      see @(see bidi-explicit-rules).")
    (xdoc::li
     "X9 and X10, which remove some characters
      and cut the paragraph into isolating run sequences;
      I1 and I2, which give the levels;
      and L1, which resets the level of white space
      at the end of a line and before separators:
      see @(see bidi-resolved-levels).")
    (xdoc::li
     "W1 to W7, about numbers and the characters around them:
      see @(see bidi-weak-types).")
    (xdoc::li
     "N0 to N2, about brackets, spaces and punctuation:
      see @(see bidi-neutral-types).")
    (xdoc::li
     "L2, which reverses stretches of text according to the levels:
      see @(see bidi-reordering)."))
   (xdoc::p
    "The functions to use are @(tsee bidi-levels)
     and @(tsee bidi-display-order),
     on a list of code points in a version of Unicode.
     The rules themselves are defined on what the algorithm
     looks at in a character, which is its bidirectional class
     and its part in a pair of brackets
     (see @(see bidi-characters)),
     and they are the same for every supported version:
     the three revisions of [UAX #9] that go with
     Unicode 16.0.0, 17.0.0 and 18.0.0
     differ in their explanations and not in their rules.
     The versions differ in the properties of the characters:
     see @(see bidi-class-property), @(see bidi-paired-brackets)
     and @(see bidi-mirroring).")
   (xdoc::p
    "What is not here:")
   (xdoc::ul
    (xdoc::li
     "Lines.
      Each paragraph is taken to be displayed on one line.
      Where a paragraph is broken into lines
      depends on the width of the display,
      and rules L1 and L2 are then applied to each line
      [UAX #9, Section 3.4].")
    (xdoc::li
     "Rule L3, about the place of combining marks,
      rule L4, which draws some characters as their mirror image
      (the property that it uses is here, but the rule is not),
      and the shaping of Arabic letters [UAX #9, Section 3.5].
      These are about how the characters are drawn,
      not about their order.")
    (xdoc::li
     "The higher-level protocols [UAX #9, Section 4.3],
      except that the direction of a paragraph can be given,
      which is protocol HL1."))
   (xdoc::p
    "There is no formal specification of the algorithm
     to prove these definitions against.
     The evidence that they are right is the two conformance files
     of the Unicode Character Database,
     @('BidiTest.txt') and @('BidiCharacterTest.txt'):
     every line of both is checked
     when the books of the library are certified,
     the first on bidirectional classes
     and the second on code points, for each supported version.
     About the algorithm itself, this library proves so far
     only that its results have the right types and lengths."))
  :order-subtopics (bidi-characters
                    bidi-explicit-rules
                    bidi-weak-types
                    bidi-neutral-types
                    bidi-resolved-levels
                    bidi-reordering))
