; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-resolved-levels")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp))) ; for the types with fields of naturals

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-reordering
  :parents (bidirectional-algorithm)
  :short "The order of display: rules P1 and L2
          of the Unicode Bidirectional Algorithm,
          and the algorithm on lists of code points."
  :long
  (xdoc::topstring
   (xdoc::p
    "Once each character of a line has its resolved level
     (see @(see bidi-resolved-levels)),
     rule L2 gives the order in which the characters are displayed,
     from left to right:
     from the highest level down to the lowest odd level,
     each longest stretch of characters at that level or higher
     is reversed [UAX #9, rule L2].
     The characters that rule X9 removed have no place in the display.")
   (xdoc::p
    "A text is first cut into paragraphs [UAX #9, rule P1],
     and each paragraph is treated by itself.
     Here each paragraph is taken to be displayed on one line:
     breaking a paragraph into lines depends on the width of the display,
     which is outside the algorithm.")
   (xdoc::p
    "The functions @(tsee bidi-levels) and @(tsee bidi-display-order)
     are the algorithm for a list of code points
     in a version of Unicode."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bidi-display-item
  :short "Fixtype of characters to display:
          the position of a character in the text, and its resolved level."
  ((position nat)
   (level nat))
  :pred bidi-display-item-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-display-item-list
  :short "Fixtype of lists of characters to display."
  :elt-type bidi-display-item
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-display-item-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-display-items ((levels bidi-level-option-listp)
                            (position natp))
  :returns (items bidi-display-item-listp)
  :short "The characters to display, in the order of the text."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the levels of the characters
     from a position on, and the second is that position.
     A character without a level, which rule X9 removed,
     is left out."))
  (b* (((when (endp levels)) nil)
       (position (lnfix position))
       (level? (acl2::maybe-natp-fix (car levels)))
       ((unless level?)
        (bidi-display-items (cdr levels) (+ 1 position))))
    (cons (make-bidi-display-item :position position :level level?)
          (bidi-display-items (cdr levels) (+ 1 position))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-display-item-list-positions ((items bidi-display-item-listp))
  :returns (positions nat-listp)
  :short "The positions of a list of characters to display."
  (if (endp items)
      nil
    (cons (bidi-display-item->position (car items))
          (bidi-display-item-list-positions (cdr items))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-highest-level ((items bidi-display-item-listp))
  :returns (level natp :rule-classes (:rewrite :type-prescription))
  :short "The highest level of a list of characters to display."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is 0 for the empty list."))
  (if (endp items)
      0
    (max (bidi-display-item->level (car items))
         (bidi-highest-level (cdr items))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-lowest-odd-level ((items bidi-display-item-listp))
  :returns (level? acl2::maybe-natp)
  :short "The lowest odd level of a list of characters to display."
  :long
  (xdoc::topstring
   (xdoc::p
    "It is @('nil') if no character of the list has an odd level."))
  (b* (((when (endp items)) nil)
       (level (bidi-display-item->level (car items)))
       (rest? (bidi-lowest-odd-level (cdr items)))
       ((when (evenp level)) rest?)
       ((unless rest?) level))
    (min level rest?))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-reverse-runs ((items bidi-display-item-listp)
                           (level natp)
                           (run bidi-display-item-listp))
  :returns (new-items bidi-display-item-listp)
  :short "Reverse each longest stretch of characters
          that are at a level or higher."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is one step of rule L2 [UAX #9, rule L2].
     The third argument is the stretch being read,
     already reversed: empty at first."))
  (b* (((when (endp items)) (bidi-display-item-list-fix run))
       (item (bidi-display-item-fix (car items)))
       ((when (>= (bidi-display-item->level item) (lnfix level)))
        (bidi-reverse-runs (cdr items) level (cons item run))))
    (append (bidi-display-item-list-fix run)
            (cons item
                  (bidi-reverse-runs (cdr items) level nil))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-reorder-items ((items bidi-display-item-listp)
                            (level natp)
                            (lowest natp))
  :returns (new-items bidi-display-item-listp)
  :short "Rule L2, from a level down to the lowest odd level."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second argument is the level to do next:
     the highest level at first.
     The third is the lowest odd level, where the rule stops."))
  (b* ((level (lnfix level))
       ((when (or (equal level 0)
                  (< level (lnfix lowest))))
        (bidi-display-item-list-fix items)))
    (bidi-reorder-items (bidi-reverse-runs items level nil)
                        (- level 1)
                        lowest))
  :measure (nfix level)
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-order-of-levels ((levels bidi-level-option-listp))
  :returns (positions nat-listp)
  :short "The order of display of the characters of a line,
          from their resolved levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is the list of the positions of the characters,
     in the order in which they are displayed from left to right;
     the position of a character is the number of characters before it
     in the line.
     The characters without a level are not displayed
     and their positions are not in the result.
     If no character has an odd level,
     nothing is reversed and the order is that of the text."))
  (b* ((items (bidi-display-items levels 0))
       (lowest? (bidi-lowest-odd-level items))
       ((unless lowest?) (bidi-display-item-list-positions items)))
    (bidi-display-item-list-positions
     (bidi-reorder-items items (bidi-highest-level items) lowest?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-paragraph-order ((chars bidi-char-listp)
                              (paragraph-level natp))
  :returns (positions nat-listp)
  :short "The order of display of the characters of a paragraph."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-paragraph-levels) and @(tsee bidi-order-of-levels)."))
  (bidi-order-of-levels (bidi-paragraph-levels chars paragraph-level))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-paragraph-length ((chars bidi-char-listp))
  :returns (length natp :rule-classes (:rewrite :type-prescription))
  :short "The number of characters of the first paragraph of a text."
  :long
  (xdoc::topstring
   (xdoc::p
    "A paragraph ends with a paragraph separator,
     a character of class @('B'), which is part of it,
     or at the end of the text [UAX #9, rule P1]."))
  (cond ((endp chars) 0)
        ((equal (bidi-class-kind (bidi-char->class (car chars)))
                :paragraph-separator)
         1)
        (t (+ 1 (bidi-paragraph-length (cdr chars)))))
  :hooks (:fix)

  ///

  (defret bidi-paragraph-length-upper-bound
    (<= length (len chars))
    :rule-classes ((:linear :trigger-terms ((bidi-paragraph-length chars))))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defret bidi-paragraph-length-lower-bound
    (implies (consp chars)
             (< 0 length))
    :rule-classes :linear
    :hints (("Goal" :expand ((bidi-paragraph-length chars))))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-levels-of-chars ((chars bidi-char-listp)
                              (direction paragraph-direction-p))
  :returns (levels bidi-level-option-listp)
  :short "The resolved levels of the characters of a text."
  :long
  (xdoc::topstring
   (xdoc::p
    "The text is cut into paragraphs [UAX #9, rule P1].
     Each paragraph gets its paragraph embedding level
     (see @(tsee bidi-paragraph-embedding-level)),
     from the direction given or from its own characters,
     and then its levels (see @(tsee bidi-paragraph-levels))."))
  (b* (((when (endp chars)) nil)
       (chars (bidi-char-list-fix chars))
       (length (bidi-paragraph-length chars))
       (paragraph (take length chars)))
    (append (bidi-paragraph-levels
             paragraph
             (bidi-paragraph-embedding-level paragraph direction))
            (bidi-levels-of-chars (nthcdr length chars) direction)))
  :measure (len chars)
  :hints (("Goal" :in-theory (enable len nfix fix natp o-p o-finp o<)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define nat-list-add ((list nat-listp) (offset natp))
  :returns (new-list nat-listp)
  :short "Add a natural to each element of a list of naturals."
  (if (endp list)
      nil
    (cons (+ (lnfix (car list)) (lnfix offset))
          (nat-list-add (cdr list) offset)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-order-of-chars ((chars bidi-char-listp)
                             (direction paragraph-direction-p)
                             (offset natp))
  :returns (positions nat-listp)
  :short "The order of display of the characters of a text."
  :long
  (xdoc::topstring
   (xdoc::p
    "The paragraphs are displayed one after the other,
     each in the order that rule L2 gives.
     The third argument is the number of characters of the text
     before the first argument: 0 at first.
     The result is a list of positions in the whole text."))
  (b* (((when (endp chars)) nil)
       (chars (bidi-char-list-fix chars))
       (length (bidi-paragraph-length chars))
       (paragraph (take length chars)))
    (append (nat-list-add
             (bidi-paragraph-order
              paragraph
              (bidi-paragraph-embedding-level paragraph direction))
             offset)
            (bidi-order-of-chars (nthcdr length chars)
                                 direction
                                 (+ (lnfix offset) length))))
  :measure (len chars)
  :hints (("Goal" :in-theory (enable len nfix fix natp o-p o-finp o<)))
  :guard-hints (("Goal" :in-theory (enable nfix)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-levels ((cps code-point-listp)
                     (direction paragraph-direction-p)
                     (ver versionp))
  :returns (levels bidi-level-option-listp)
  :short "The resolved levels of a list of code points,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result has an element for each code point:
     its resolved level [UAX #9, Section 3.3],
     or @('nil') if rule X9 removes it.
     Text at an even level is displayed from left to right,
     and text at an odd level from right to left.
     The second argument gives the direction of every paragraph,
     or says that each paragraph finds its own."))
  (bidi-levels-of-chars (code-points-to-bidi-chars cps ver) direction)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-display-order ((cps code-point-listp)
                            (direction paragraph-direction-p)
                            (ver versionp))
  :returns (positions nat-listp)
  :short "The order in which a list of code points is displayed,
          in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is a list of positions in the list of code points,
     where the position of a code point is the number of code points
     before it.
     It gives, paragraph after paragraph,
     the code points of the paragraph from left to right
     as the Unicode Bidirectional Algorithm orders them
     [UAX #9, Section 3.4],
     when each paragraph is on one line.
     The code points that rule X9 removes are not in the result.")
   (xdoc::p
    "For example, for the three code points
     U+0061, U+05D0 and U+05D1,
     a Latin letter and two Hebrew letters,
     in a paragraph from left to right,
     the result is the list of 0, 2 and 1:
     the two Hebrew letters are displayed with the second one on the left."))
  (bidi-order-of-chars (code-points-to-bidi-chars cps ver) direction 0)
  :hooks (:fix))
