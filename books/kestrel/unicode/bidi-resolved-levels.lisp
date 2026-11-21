; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-explicit-levels")
(include-book "bidi-weak-types")
(include-book "bidi-neutral-types")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp))) ; for the types with fields of naturals

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-resolved-levels
  :parents (bidirectional-algorithm)
  :short "The resolved levels of a paragraph:
          rules X9 and X10, I1 and I2, and L1
          of the Unicode Bidirectional Algorithm."
  :long
  (xdoc::topstring
   (xdoc::p
    "After the explicit levels (see @(see bidi-explicit-rules)),
     the algorithm removes the characters of some classes [UAX #9, rule X9]
     and cuts what is left of the paragraph into isolating run sequences
     [UAX #9, BD13 and rule X10].
     A level run is a longest stretch of characters next to each other
     with the same level [UAX #9, BD7].
     An isolating run sequence is one level run,
     or several that are joined across isolates:
     a level run that ends with an isolate initiator
     is followed, in the sequence, by the level run that starts
     with the matching @('PDI').
     So the text inside an isolate, which is at a higher level,
     is left out, and the text around it is treated as if it were together.")
   (xdoc::p
    "The rules for the weak types (see @(see bidi-weak-types))
     and for the neutral types (see @(see bidi-neutral-types))
     are applied to each isolating run sequence by itself.
     Then rules I1 and I2 give each character its level,
     from the level of the sequence and the class
     that the character has ended up with.
     Last, rule L1 puts some characters back
     at the paragraph embedding level.")
   (xdoc::p
    "A position, in this book, is the number of characters before it
     in the paragraph as it is after rule X9."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bidi-leveled-char
  :short "Fixtype of characters with what rules X1 to X8 found about them."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the bidirectional class of the character,
     its class after the overrides,
     its role in a bracket pair,
     and its explicit embedding level."))
  ((original bidi-class)
   (class bidi-class)
   (bracket bidi-bracket-role)
   (level nat))
  :pred bidi-leveled-char-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-leveled-char-list
  :short "Fixtype of lists of characters
          with what rules X1 to X8 found about them."
  :elt-type bidi-leveled-char
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-leveled-char-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-level-option-list
  :short "Fixtype of lists of optional embedding levels."
  :long
  (xdoc::topstring
   (xdoc::p
    "The value @('nil') is for a character that rule X9 removes,
     which has no level."))
  :elt-type acl2::maybe-nat
  :true-listp t
  :elementp-of-nil t
  :pred bidi-level-option-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-leveled-chars ((chars bidi-char-listp)
                            (levels nat-listp)
                            (classes bidi-class-listp))
  :returns (lchars bidi-leveled-char-listp)
  :short "Put the characters of a paragraph together with
          their explicit levels and their classes after the overrides."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second and third arguments are the two results
     of @(tsee bidi-explicit-levels)."))
  (b* (((when (or (endp chars)
                  (endp levels)
                  (endp classes)))
        nil)
       ((bidi-char char) (car chars)))
    (cons (make-bidi-leveled-char :original char.class
                                  :class (car classes)
                                  :bracket char.bracket
                                  :level (car levels))
          (bidi-leveled-chars (cdr chars) (cdr levels) (cdr classes))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-remove-by-x9 ((lchars bidi-leveled-char-listp))
  :returns (kept bidi-leveled-char-listp)
  :short "Rule X9: remove the characters of the embeddings and overrides,
          and those of class @('BN')."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee bidi-class-removed-p) for the classes.
     It is the class of the character itself that counts,
     not the class that an override may have given it."))
  (cond ((endp lchars) nil)
        ((bidi-class-removed-p (bidi-leveled-char->original (car lchars)))
         (bidi-remove-by-x9 (cdr lchars)))
        (t (cons (bidi-leveled-char-fix (car lchars))
                 (bidi-remove-by-x9 (cdr lchars)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-leveled-char-list-levels ((lchars bidi-leveled-char-listp))
  :returns (levels nat-listp)
  :short "The explicit levels of a list of characters."
  (if (endp lchars)
      nil
    (cons (bidi-leveled-char->level (car lchars))
          (bidi-leveled-char-list-levels (cdr lchars))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-leveled-char-list-levels
    (equal (len levels)
           (len lchars))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-leveled-char-list-classes ((lchars bidi-leveled-char-listp))
  :returns (classes bidi-class-listp)
  :short "The classes, after the overrides, of a list of characters."
  (if (endp lchars)
      nil
    (cons (bidi-leveled-char->class (car lchars))
          (bidi-leveled-char-list-classes (cdr lchars))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-leveled-char-list-classes
    (equal (len classes)
           (len lchars))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-leveled-char-list-brackets ((lchars bidi-leveled-char-listp))
  :returns (roles bidi-bracket-role-listp)
  :short "The roles in bracket pairs of a list of characters."
  (if (endp lchars)
      nil
    (cons (bidi-leveled-char->bracket (car lchars))
          (bidi-leveled-char-list-brackets (cdr lchars))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-leveled-char-at ((position natp)
                              (lchars bidi-leveled-char-listp))
  :returns (lchar bidi-leveled-char-p)
  :short "The character at a position of a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a position that is not in the list,
     the result is a character of class @('L') at level 0,
     which stands for nothing:
     the functions of this book ask only for positions in the list,
     or check first."))
  (b* ((position (lnfix position))
       ((when (endp lchars))
        (make-bidi-leveled-char :original (bidi-class-left-to-right)
                                :class (bidi-class-left-to-right)
                                :bracket (bidi-bracket-role-none)
                                :level 0))
       ((when (equal position 0)) (bidi-leveled-char-fix (car lchars))))
    (bidi-leveled-char-at (- position 1) (cdr lchars)))
  :measure (acl2-count lchars)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-leveled-chars-at ((positions nat-listp)
                               (lchars bidi-leveled-char-listp))
  :returns (selected bidi-leveled-char-listp)
  :short "The characters at a list of positions of a list."
  (if (endp positions)
      nil
    (cons (bidi-leveled-char-at (car positions) lchars)
          (bidi-leveled-chars-at (cdr positions) lchars)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-leveled-chars-at
    (equal (len selected)
           (len positions))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-implicit-level ((class bidi-class-p) (level natp))
  :returns (new-level natp :rule-classes (:rewrite :type-prescription))
  :short "Rules I1 and I2: the level of a character,
          from its class and the level of its isolating run sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "At an even level, a character of class @('R') goes up one level,
     and a number, @('AN') or @('EN'), goes up two [UAX #9, rule I1].
     At an odd level, a character of class @('L'), @('EN') or @('AN')
     goes up one level [UAX #9, rule I2].
     After the rules for the weak and the neutral types,
     these are the only classes that are left."))
  (b* ((level (lnfix level)))
    (if (evenp level)
        (bidi-class-case class
                         :right-to-left (+ 1 level)
                         :arabic-number (+ 2 level)
                         :european-number (+ 2 level)
                         :otherwise level)
      (bidi-class-case class
                       :left-to-right (+ 1 level)
                       :european-number (+ 1 level)
                       :arabic-number (+ 1 level)
                       :otherwise level)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-implicit-levels ((classes bidi-class-listp) (level natp))
  :returns (levels nat-listp)
  :short "Rules I1 and I2 on the characters of an isolating run sequence."
  (if (endp classes)
      nil
    (cons (bidi-implicit-level (car classes) level)
          (bidi-implicit-levels (cdr classes) level)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-implicit-levels
    (equal (len levels)
           (len classes))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-resolve-sequence ((classes bidi-class-listp)
                               (roles bidi-bracket-role-listp)
                               (sos bidi-class-p)
                               (eos bidi-class-p)
                               (level natp))
  :returns (levels nat-listp)
  :short "The resolved levels of the characters
          of one isolating run sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the classes of the characters of the sequence,
     after the overrides;
     their roles in bracket pairs;
     the classes @('sos') and @('eos'),
     each @('L') or @('R'),
     which stand for the text before and after the sequence;
     and the embedding level of the sequence.
     Rules W1 to W7, N0 to N2, and I1 and I2 are applied in that order,
     each to the whole sequence [UAX #9, rule X10]."))
  (b* ((embedding (bidi-level-direction level))
       (weak (bidi-resolve-weak-types classes sos))
       (neutral (bidi-resolve-neutral-types weak
                                            classes
                                            roles
                                            sos
                                            eos
                                            embedding)))
    (bidi-implicit-levels neutral level))
  :hooks (:fix)

  ///

  (defret len-of-bidi-resolve-sequence
    (equal (len levels)
           (len classes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-matching-pdi ((lchars bidi-leveled-char-listp)
                           (depth natp))
  :returns (offset? acl2::maybe-natp)
  :short "Find the matching @('PDI') of an isolate initiator."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the characters
     after the isolate initiator, and the second is 0.
     The result is the number of characters before the matching @('PDI')
     in that list, or @('nil') if there is none.")
   (xdoc::p
    "The matching @('PDI') is found by counting [UAX #9, BD9]:
     the specification starts a counter at one,
     adds one at each isolate initiator,
     takes one away at each @('PDI'),
     and the matching @('PDI') is the first one
     that brings the counter to zero.
     The second argument is that counter less one:
     the number of isolates that have been opened since
     and are not closed yet.
     The characters count as what they are,
     not as the classes that an override may have given them."))
  (b* (((when (endp lchars)) nil)
       (depth (lnfix depth))
       (original (bidi-leveled-char->original (car lchars)))
       (pdi (equal (bidi-class-kind original) :pop-directional-isolate))
       ((when (and pdi (equal depth 0))) 0)
       (offset? (bidi-matching-pdi (cdr lchars)
                                   (cond ((bidi-class-isolate-initiator-p
                                           original)
                                          (+ 1 depth))
                                         (pdi (- depth 1))
                                         (t depth)))))
    (and offset?
         (+ 1 offset?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-open-isolates ((lchars bidi-leveled-char-listp)
                            (count natp)
                            (depth natp))
  :returns (new-depth natp :rule-classes (:rewrite :type-prescription))
  :short "The number of isolate initiators, among the first characters
          of a list, whose matching @('PDI') is not among them."
  :long
  (xdoc::topstring
   (xdoc::p
    "The second argument is how many characters of the list to look at.
     The third is the number found so far: 0 at first.
     It goes up at each isolate initiator,
     and down at each @('PDI') if it is not zero;
     a @('PDI') met when it is zero matches no isolate initiator
     [UAX #9, BD9].")
   (xdoc::p
    "So the character that comes after those looked at,
     if it is a @('PDI'), matches an isolate initiator
     exactly when the result is not zero."))
  (b* ((count (lnfix count))
       (depth (lnfix depth))
       ((when (or (equal count 0)
                  (endp lchars)))
        depth)
       (original (bidi-leveled-char->original (car lchars))))
    (bidi-open-isolates
     (cdr lchars)
     (- count 1)
     (cond ((bidi-class-isolate-initiator-p original) (+ 1 depth))
           ((and (equal (bidi-class-kind original) :pop-directional-isolate)
                 (> depth 0))
            (- depth 1))
           (t depth))))
  :measure (acl2-count lchars)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-sequence-successor ((position natp)
                                 (lchars bidi-leveled-char-listp))
  :returns (next? acl2::maybe-natp)
  :short "The position that follows a position
          in its isolating run sequence."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the next character of the paragraph has the same level,
     it is in the same level run, and its position is the result.
     Otherwise the level run ends here.
     Then, if the character is an isolate initiator
     that has a matching @('PDI'),
     the sequence goes on with the level run
     that starts with that @('PDI'),
     and its position is the result [UAX #9, BD13].
     Otherwise the sequence ends here, and the result is @('nil').")
   (xdoc::p
    "An isolate initiator that has had no effect, because of the depth limit,
     is followed by characters at its own level, up to its matching @('PDI'):
     they are all in one level run,
     and the first case applies to each of them."))
  (b* ((position (lnfix position))
       ((unless (< position (len lchars))) nil)
       ((bidi-leveled-char this) (bidi-leveled-char-at position lchars))
       ((when (and (< (+ 1 position) (len lchars))
                   (equal (bidi-leveled-char->level
                           (bidi-leveled-char-at (+ 1 position) lchars))
                          this.level)))
        (+ 1 position))
       ((unless (bidi-class-isolate-initiator-p this.original)) nil)
       (offset? (bidi-matching-pdi
                 (nthcdr (+ 1 position) (bidi-leveled-char-list-fix lchars))
                 0)))
    (and offset?
         (+ 1 position offset?)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-sequence-from ((position natp)
                            (lchars bidi-leveled-char-listp))
  :returns (positions nat-listp)
  :short "The positions of an isolating run sequence, from one of them on."
  :long
  (xdoc::topstring
   (xdoc::p
    "This follows @(tsee bidi-sequence-successor)
     until the sequence ends.
     The result is empty if the position is not in the paragraph."))
  (b* ((position (lnfix position))
       ((unless (< position (len lchars))) nil)
       (next? (bidi-sequence-successor position lchars))
       ((unless (and next?
                     (< position next?)))
        (list position)))
    (cons position
          (bidi-sequence-from next? lchars)))
  :measure (nfix (- (len lchars) (nfix position)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-sequence-start-p ((position natp)
                               (lchars bidi-leveled-char-listp))
  :returns (yes/no booleanp)
  :short "Check if an isolating run sequence starts at a position."
  :long
  (xdoc::topstring
   (xdoc::p
    "A sequence starts with each level run whose first character
     is not a @('PDI'),
     or is a @('PDI') that matches no isolate initiator [UAX #9, BD13].
     A level run starts at the first character of the paragraph,
     and wherever the character before has another level."))
  (b* ((position (lnfix position))
       ((unless (< position (len lchars))) nil)
       ((bidi-leveled-char this) (bidi-leveled-char-at position lchars))
       ((unless (or (equal position 0)
                    (not (equal (bidi-leveled-char->level
                                 (bidi-leveled-char-at (- position 1)
                                                       lchars))
                                this.level))))
        nil)
       ((unless (equal (bidi-class-kind this.original)
                       :pop-directional-isolate))
        t))
    (equal (bidi-open-isolates lchars position 0) 0))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-level-at ((position natp)
                       (lchars bidi-leveled-char-listp)
                       (paragraph-level natp))
  :returns (level natp :rule-classes (:rewrite :type-prescription))
  :short "The explicit level of the character at a position,
          or the paragraph embedding level if there is no such character."
  (if (< (lnfix position) (len lchars))
      (bidi-leveled-char->level (bidi-leveled-char-at position lchars))
    (lnfix paragraph-level))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define nat-list-last ((list nat-listp))
  :returns (last natp :rule-classes (:rewrite :type-prescription))
  :short "The last element of a list of naturals, or 0 if it is empty."
  (cond ((endp list) 0)
        ((endp (cdr list)) (lnfix (car list)))
        (t (nat-list-last (cdr list))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-resolve-sequence-at ((positions nat-listp)
                                  (lchars bidi-leveled-char-listp)
                                  (paragraph-level natp))
  :returns (levels nat-listp)
  :short "The resolved levels of the characters
          of the isolating run sequence at a list of positions."
  :long
  (xdoc::topstring
   (xdoc::p
    "This finds @('sos') and @('eos') [UAX #9, rule X10]
     and calls @(tsee bidi-resolve-sequence).")
   (xdoc::p
    "For @('sos'), the level of the first character of the sequence
     is compared with the level of the character before it
     in the paragraph, or with the paragraph embedding level
     if it is the first of the paragraph.
     For @('eos'), the level of the last character of the sequence
     is compared with the level of the character after it
     in the paragraph, or with the paragraph embedding level
     if it is the last of the paragraph
     or if it is an isolate initiator.
     In each case, the higher of the two levels decides:
     @('R') if it is odd, @('L') if it is even.
     The levels are the explicit levels,
     and the paragraph is the paragraph after rule X9."))
  (b* (((when (endp positions)) nil)
       (first (lnfix (car positions)))
       (last (nat-list-last positions))
       (sequence (bidi-leveled-chars-at positions lchars))
       ((bidi-leveled-char first-char) (bidi-leveled-char-at first lchars))
       ((bidi-leveled-char last-char) (bidi-leveled-char-at last lchars))
       (before (if (equal first 0)
                   (lnfix paragraph-level)
                 (bidi-level-at (- first 1) lchars paragraph-level)))
       (after (if (bidi-class-isolate-initiator-p last-char.original)
                  (lnfix paragraph-level)
                (bidi-level-at (+ 1 last) lchars paragraph-level))))
    (bidi-resolve-sequence
     (bidi-leveled-char-list-classes sequence)
     (bidi-leveled-char-list-brackets sequence)
     (bidi-level-direction (max first-char.level before))
     (bidi-level-direction (max last-char.level after))
     first-char.level))
  :hooks (:fix)

  ///

  (defret len-of-bidi-resolve-sequence-at
    (equal (len levels)
           (len positions))
    :hints (("Goal" :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define nat-list-set ((position natp) (value natp) (list nat-listp))
  :returns (new-list nat-listp)
  :short "Replace the element at a position of a list of naturals."
  :long
  (xdoc::topstring
   (xdoc::p
    "The list is unchanged if the position is not in it."))
  (b* ((position (lnfix position))
       ((when (endp list)) nil)
       ((when (equal position 0))
        (cons (lnfix value)
              (nat-list-fix (cdr list)))))
    (cons (lnfix (car list))
          (nat-list-set (- position 1) value (cdr list))))
  :measure (acl2-count list)
  :hooks (:fix)

  ///

  (defret len-of-nat-list-set
    (equal (len new-list)
           (len list))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define nat-list-set-list ((positions nat-listp)
                           (values nat-listp)
                           (list nat-listp))
  :returns (new-list nat-listp)
  :short "Replace the elements at a list of positions
          of a list of naturals."
  (b* (((when (or (endp positions)
                  (endp values)))
        (nat-list-fix list)))
    (nat-list-set-list (cdr positions)
                       (cdr values)
                       (nat-list-set (car positions) (car values) list)))
  :hooks (:fix)

  ///

  (defret len-of-nat-list-set-list
    (equal (len new-list)
           (len list))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-resolve-sequences-from ((position natp)
                                     (lchars bidi-leveled-char-listp)
                                     (paragraph-level natp)
                                     (levels nat-listp))
  :returns (new-levels nat-listp)
  :short "Resolve the levels of the isolating run sequences
          that start at a position or after it."
  :long
  (xdoc::topstring
   (xdoc::p
    "The last argument is the list of the levels of the characters
     of the paragraph: at first their explicit levels.
     For each position where a sequence starts
     (see @(tsee bidi-sequence-start-p)),
     the levels of the characters of that sequence
     are replaced by their resolved levels.
     Each character is in exactly one sequence [UAX #9, BD13],
     so at the end every level has been replaced once."))
  (b* ((position (lnfix position))
       ((unless (< position (len lchars))) (nat-list-fix levels))
       ((unless (bidi-sequence-start-p position lchars))
        (bidi-resolve-sequences-from (+ 1 position)
                                     lchars
                                     paragraph-level
                                     levels))
       (positions (bidi-sequence-from position lchars)))
    (bidi-resolve-sequences-from
     (+ 1 position)
     lchars
     paragraph-level
     (nat-list-set-list positions
                        (bidi-resolve-sequence-at positions
                                                  lchars
                                                  paragraph-level)
                        levels)))
  :measure (nfix (- (len lchars) (nfix position)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-resolve-sequences-from
    (equal (len new-levels)
           (len levels))
    :hints (("Goal" :induct t))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-reset-levels ((lchars bidi-leveled-char-listp)
                           (levels nat-listp)
                           (paragraph-level natp))
  :returns (mv (new-levels nat-listp)
               (trailing booleanp))
  :short "Rule L1: put the separators and the white space before them
          and at the end at the paragraph embedding level."
  :long
  (xdoc::topstring
   (xdoc::p
    "The level becomes the paragraph embedding level
     for each segment separator (@('S'))
     and paragraph separator (@('B')),
     and for each sequence of white space (@('WS'))
     and isolate formatting characters
     that comes just before one of those or at the end of the line
     [UAX #9, rule L1].
     The classes are those of the characters themselves.
     The paragraph is taken to be on one line.")
   (xdoc::p
    "The second result says whether everything from the start
     of the list to the next separator, or to the end,
     is white space or isolate formatting characters."))
  (b* (((when (or (endp lchars)
                  (endp levels)))
        (mv nil t))
       ((mv rest trailing)
        (bidi-reset-levels (cdr lchars) (cdr levels) paragraph-level))
       (original (bidi-leveled-char->original (car lchars)))
       (level (lnfix (car levels)))
       (paragraph-level (lnfix paragraph-level)))
    (cond ((or (equal (bidi-class-kind original) :segment-separator)
               (equal (bidi-class-kind original) :paragraph-separator))
           (mv (cons paragraph-level rest) t))
          ((or (equal (bidi-class-kind original) :white-space)
               (bidi-class-isolate-formatting-p original))
           (mv (cons (if trailing paragraph-level level) rest)
               trailing))
          (t (mv (cons level rest) nil))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-expand-levels ((originals bidi-class-listp)
                            (levels nat-listp))
  :returns (all-levels bidi-level-option-listp)
  :short "Give each character of a paragraph its level,
          or @('nil') if rule X9 removed it."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the classes
     of all the characters of the paragraph,
     and the second is the list of the levels
     of those that rule X9 did not remove."))
  (cond ((endp originals) nil)
        ((bidi-class-removed-p (car originals))
         (cons nil
               (bidi-expand-levels (cdr originals) levels)))
        ((endp levels)
         (cons nil
               (bidi-expand-levels (cdr originals) nil)))
        (t (cons (lnfix (car levels))
                 (bidi-expand-levels (cdr originals) (cdr levels)))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-expand-levels
    (equal (len all-levels)
           (len originals))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-paragraph-levels ((chars bidi-char-listp)
                               (paragraph-level natp))
  :returns (levels bidi-level-option-listp)
  :short "The resolved levels of the characters of a paragraph."
  :long
  (xdoc::topstring
   (xdoc::p
    "The arguments are the characters of one paragraph
     and the paragraph embedding level
     (see @(tsee bidi-paragraph-embedding-level)).
     The result has, for each character, its resolved level,
     or @('nil') if rule X9 removes the character.
     These are the levels as they are after rule L1,
     for a paragraph that is displayed on one line.")
   (xdoc::p
    "The steps are: the explicit levels (rules X1 to X8);
     the removal of some characters (rule X9);
     the resolution of each isolating run sequence
     (rule X10, with rules W1 to W7, N0 to N2, I1 and I2);
     and rule L1."))
  (b* ((originals (bidi-char-list-classes chars))
       ((mv explicit-levels classes)
        (bidi-explicit-levels originals paragraph-level))
       (lchars (bidi-remove-by-x9
                (bidi-leveled-chars chars explicit-levels classes)))
       (levels (bidi-resolve-sequences-from
                0
                lchars
                paragraph-level
                (bidi-leveled-char-list-levels lchars)))
       ((mv levels &) (bidi-reset-levels lchars levels paragraph-level)))
    (bidi-expand-levels originals levels))
  :hooks (:fix)

  ///

  (defret len-of-bidi-paragraph-levels
    (equal (len levels)
           (len chars))))
