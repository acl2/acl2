; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-left-to-right")
(include-book "bidi-confinement")
(include-book "bidi-guarded-theorem")
(include-book "bidi-self-contained")
(include-book "bidi-rule")
(include-book "bidi-rule-display")

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
      see @(see bidi-reordering).")
    (xdoc::li
     "L3, which puts combining marks after their base characters,
      and L4, which draws some characters as their mirror image:
      see @(see bidi-displayed-text)."))
   (xdoc::p
    "The functions to use are @(tsee bidi-levels)
     and @(tsee bidi-display-order),
     on a list of code points in a version of Unicode,
     for the levels and for the order
     of the characters that have a level;
     and @(tsee bidi-display),
     for the whole text as it is displayed,
     with the characters that the algorithm gives no level.
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
     "The shaping of Arabic letters [UAX #9, Section 3.5],
      which is about how the characters are drawn.")
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
     The two files test the levels and the order;
     they do not test rules L3 and L4
     or the place of the characters without a level,
     where the specification leaves some room:
     see @(see bidi-displayed-text) for the choices made here.")
   (xdoc::p
    "About the algorithm itself, this library proves the following:")
   (xdoc::ul
    (xdoc::li
     "The algorithm only rearranges.
      The order of display is a permutation of the positions
      of the characters that have a level:
      each of them is displayed once
      (see @(see bidi-rearrangement)).
      And the text as displayed, before rule L4,
      has the code points of the text as stored, in another order,
      so it has the same length
      (see @(see bidi-display-theorems)).")
    (xdoc::li
     "Text with no character
      that can make text be displayed from right to left,
      in a paragraph that is not set from right to left,
      is displayed as it is stored:
      every level is even, the order of display is the stored order,
      and no character is replaced
      (see @(see right-to-left-free) and @(see bidi-left-to-right)).
      The condition is on the @('Bidi_Class') of each character,
      so it can be checked without running the algorithm.")
    (xdoc::li
     "The algorithm does not move a character across a clean cut.
      In a paragraph from left to right,
      if the character before a place of the text
      or the character after it has level 0,
      the characters stored before that place
      are the characters displayed to the left of it, in another order.
      So a text cut into segments at such places
      is displayed segment by segment
      (see @(see bidi-confinement)).")
    (xdoc::li
     "For a plain text (see @(tsee bidi-plain-p)),
      there are conditions on the segments
      under which every cut between two segments is such a place.
      They are on the @('Bidi_Class') of each character
      and on the bracket pairs of the text,
      so they can be checked without running the algorithm;
      the proof goes through the rules one by one
      (see @(see bidi-guarded-segments)
      and @(see bidi-guarded-segments-theorem)).")
    (xdoc::li
     "With two more conditions on the bracket pairs of a plain text,
      which can also be checked without running the algorithm,
      each segment is displayed as it is alone:
      in a paragraph from left to right,
      each character has the level
      that it has when its segment is a paragraph of its own,
      and the display of the text is the display of the first segment,
      followed by the display of the second segment, and so on
      (see @(see bidi-self-contained-segments)
      and @(see bidi-self-contained-segments-theorem))."))
   (xdoc::p
    "The library also has the Bidi Rule,
     the condition that Internationalized Domain Names put
     on a label with right-to-left characters,
     and two rules derived from it
     for which a search finds no two labels that are displayed alike
     (see @(see bidi-rule)).
     Those predicates look only at the classes of the characters.
     That the two derived rules keep any two different labels
     from being displayed alike is not proved yet.
     For the wider of the two, a part of the proof is done:
     the display of a name is said directly,
     and that display is proved to be different for different names
     (see @(see bidi-rule-display))."))
  :order-subtopics (bidi-characters
                    bidi-explicit-rules
                    bidi-weak-types
                    bidi-neutral-types
                    bidi-resolved-levels
                    bidi-reordering
                    bidi-displayed-text
                    bidi-rearrangement
                    right-to-left-free
                    bidi-left-to-right
                    bidi-confinement
                    bidi-rule))
