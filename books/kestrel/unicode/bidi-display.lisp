; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rearrangement")
(include-book "bidi-mirroring")
(include-book "general-category")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp))) ; for the types with fields of naturals

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bidi-displayed-text
  :parents (bidirectional-algorithm)
  :short "The text as it is displayed, with every character kept:
          the levels of the characters that rule X9 removes,
          and rules L3 and L4 of the Unicode Bidirectional Algorithm."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @(tsee bidi-display-order) gives the order of display
     of the characters that have a level.
     Some uses need the whole text in the order of display,
     with the characters that rule X9 removes too:
     the bidirectional skeleton of [UTS #39, Section 4] is one,
     since it reorders the code points of a string, all of them.
     This book has that, in the function @(tsee bidi-display).
     It makes three choices where the specifications
     leave room, and each is stated here.")
   (xdoc::p
    "First, the characters that rule X9 removes.
     The rule says that an implementation need not remove them,
     and that their place on the display is not specified.
     [UAX #9, Section 5.2] describes how to keep them,
     as a guideline and not as a requirement:
     such a character takes the level of the character before it,
     or the paragraph embedding level if it is the first of the paragraph;
     and in rule L1 it counts with the white space,
     so that it is put back at the paragraph embedding level
     at the end of a line or before a separator.
     We follow that guideline;
     see @(tsee bidi-paragraph-all-levels).
     The levels of the other characters are not affected.
     Implementations differ here:
     some give such a character the level of the character after it.")
   (xdoc::p
    "Second, rule L3 [UAX #9, rule L3].
     After rule L2, a combining mark on a base character
     at a right-to-left level comes before its base in the order of display.
     The rule says that if the marks are expected after their bases,
     the order of the marks and the base must be reversed,
     and [UTS #39, Section 4] applies it in those words:
     move combining marks after their base.
     Neither says exactly which characters are meant.
     We take a combining mark to be a character whose
     @('General_Category') is a mark [Unicode, Section 3.6, D52],
     and the base of some marks to be the character
     that comes right after them in the order of display,
     if it is not a mark and is at the same odd level as they are.
     Marks at an odd level that have no such base,
     of which the rule does not speak,
     are put back in the order in which they are stored,
     as the marks of a base are.
     So at an odd level each sequence of a base and its marks,
     or of marks alone, reads as it is stored;
     see @(tsee bidi-move-marks).")
   (xdoc::p
    "Third, rule L4 [UAX #9, rule L4]:
     a character at an odd level that has the property @('Bidi_Mirrored')
     is drawn as its mirror image.
     Here it is replaced by its @('Bidi_Mirroring_Glyph'), if it has one,
     as [UTS #39, Section 4] does;
     a character with @('Bidi_Mirrored') and no mirroring glyph is kept.
     See @(tsee bidi-mirror-char) and @(see bidi-mirroring).")
   (xdoc::p
    "As in @(see bidi-reordering),
     each paragraph is taken to be displayed on one line."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod bidi-shown-char
  :short "Fixtype of characters with their levels:
          a code point and the level at which it is displayed."
  ((code-point code-point)
   (level nat))
  :pred bidi-shown-char-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-shown-char-list
  :short "Fixtype of lists of characters with their levels."
  :elt-type bidi-shown-char
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-shown-char-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local (in-theory (disable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel natp-of-maybe-natp-fix
  (implies (acl2::maybe-natp-fix x)
           (natp (acl2::maybe-natp-fix x)))
  :enable (acl2::maybe-natp-fix natp nfix))

(define bidi-fill-levels ((levels bidi-level-option-listp)
                          (previous natp))
  :returns (all-levels nat-listp)
  :short "Give a level to the characters that rule X9 removes:
          the level of the character before."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is the list of the levels of the characters
     of a paragraph from some character on,
     and the second is the level of the character before those,
     or the paragraph embedding level at the start of the paragraph.
     A character without a level takes the level of the character before it,
     which may have got its level in the same way
     [UAX #9, Section 5.2]."))
  (b* (((when (endp levels)) nil)
       (level (or (acl2::maybe-natp-fix (car levels))
                  (lnfix previous))))
    (cons level
          (bidi-fill-levels (cdr levels) level)))
  :hooks (:fix)

  ///

  (defret len-of-bidi-fill-levels
    (equal (len all-levels)
           (len levels))
    :hints (("Goal" :induct t :in-theory (enable len)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-reset-all-levels ((classes bidi-class-listp)
                               (levels nat-listp)
                               (paragraph-level natp))
  :returns (mv (new-levels nat-listp)
               (trailing booleanp))
  :short "Rule L1 for a paragraph with every character kept."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is rule L1 (see @(tsee bidi-reset-levels))
     with the characters that rule X9 removes
     counted with the white space and the isolate formatting characters
     [UAX #9, Section 5.2]:
     a sequence of such characters just before a separator,
     or at the end of the paragraph,
     is put at the paragraph embedding level.
     The first argument is the list of the classes
     of all the characters of the paragraph,
     and the second the list of their levels.")
   (xdoc::p
    "The second result says whether everything from the start
     of the list to the next separator, or to the end,
     is of those classes."))
  (b* (((when (or (endp classes)
                  (endp levels)))
        (mv nil t))
       ((mv rest trailing)
        (bidi-reset-all-levels (cdr classes) (cdr levels) paragraph-level))
       (class (bidi-class-fix (car classes)))
       (level (lnfix (car levels)))
       (paragraph-level (lnfix paragraph-level)))
    (cond ((or (equal (bidi-class-kind class) :segment-separator)
               (equal (bidi-class-kind class) :paragraph-separator))
           (mv (cons paragraph-level rest) t))
          ((or (equal (bidi-class-kind class) :white-space)
               (bidi-class-isolate-formatting-p class)
               (bidi-class-removed-p class))
           (mv (cons (if trailing paragraph-level level) rest)
               trailing))
          (t (mv (cons level rest) nil))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-reset-all-levels
    (implies (equal (len levels) (len classes))
             (equal (len new-levels)
                    (len classes)))
    :hints (("Goal" :induct t :in-theory (enable len fix)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-paragraph-all-levels ((chars bidi-char-listp)
                                   (paragraph-level natp))
  :returns (levels nat-listp)
  :short "The levels of all the characters of a paragraph,
          with those that rule X9 removes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A character that has a level by the rules of the algorithm
     (see @(tsee bidi-paragraph-levels)) keeps it.
     A character that rule X9 removes gets a level
     as [UAX #9, Section 5.2] describes:
     see @(tsee bidi-fill-levels) and @(tsee bidi-reset-all-levels)."))
  (b* ((levels (bidi-fill-levels
                (bidi-paragraph-levels chars paragraph-level)
                paragraph-level))
       ((mv levels &)
        (bidi-reset-all-levels (bidi-char-list-classes chars)
                               levels
                               paragraph-level)))
    levels)
  :hooks (:fix)

  ///

  (defret len-of-bidi-paragraph-all-levels
    (equal (len levels)
           (len chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-shown-chars ((cps code-point-listp) (levels nat-listp))
  :returns (shown bidi-shown-char-listp)
  :short "Put code points together with their levels."
  (b* (((when (or (endp cps)
                  (endp levels)))
        nil))
    (cons (make-bidi-shown-char :code-point (car cps)
                                :level (car levels))
          (bidi-shown-chars (cdr cps) (cdr levels))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-shown-chars
    (implies (equal (len levels) (len cps))
             (equal (len shown)
                    (len cps)))
    :hints (("Goal" :induct t :in-theory (enable len fix)))))

;;;;;;;;;;;;;;;;;;;;

(define bidi-shown-char-list-code-points ((shown bidi-shown-char-listp))
  :returns (cps code-point-listp)
  :short "The code points of a list of characters with their levels."
  (if (endp shown)
      nil
    (cons (bidi-shown-char->code-point (car shown))
          (bidi-shown-char-list-code-points (cdr shown))))
  :hooks (:fix)

  ///

  (defret len-of-bidi-shown-char-list-code-points
    (equal (len cps)
           (len shown))
    :hints (("Goal" :induct t :in-theory (enable len))))

  (defrule bidi-shown-char-list-code-points-of-append
    (equal (bidi-shown-char-list-code-points (append shown1 shown2))
           (append (bidi-shown-char-list-code-points shown1)
                   (bidi-shown-char-list-code-points shown2)))
    :induct (len shown1)
    :enable (append len))

  (defrule bidi-shown-char-list-code-points-of-bidi-shown-chars
    (implies (equal (len levels) (len cps))
             (equal (bidi-shown-char-list-code-points
                     (bidi-shown-chars cps levels))
                    (code-point-list-fix cps)))
    :induct (bidi-shown-chars cps levels)
    :enable (bidi-shown-chars code-point-list-fix len fix)))

;;;;;;;;;;;;;;;;;;;;

(define bidi-shown-char-at ((position natp)
                            (shown bidi-shown-char-listp))
  :returns (char bidi-shown-char-p)
  :short "The character at a position of a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "For a position that is not in the list,
     the result is the code point 0 at level 0, which stands for nothing:
     the positions that this book asks for are in the list."))
  (b* ((position (lnfix position))
       ((when (endp shown))
        (make-bidi-shown-char :code-point 0 :level 0))
       ((when (equal position 0)) (bidi-shown-char-fix (car shown))))
    (bidi-shown-char-at (- position 1) (cdr shown)))
  :measure (acl2-count shown)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-shown-chars-at ((positions nat-listp)
                             (shown bidi-shown-char-listp))
  :returns (selected bidi-shown-char-listp)
  :short "The characters at a list of positions of a list, in that order."
  (if (endp positions)
      nil
    (cons (bidi-shown-char-at (car positions) shown)
          (bidi-shown-chars-at (cdr positions) shown)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define bidi-combining-mark-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  :short "Check if a code point is a combining mark, for rule L3."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, if its @('General_Category') is
     @('Nonspacing_Mark'), @('Spacing_Mark') or @('Enclosing_Mark')
     [Unicode, Section 3.6, D52]."))
  (general-category-mark-p (code-point-general-category cp ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defrulel bidi-shown-char-list-fix-when-not-consp
  (implies (not (consp x))
           (equal (bidi-shown-char-list-fix x)
                  nil))
  :enable bidi-shown-char-list-fix)

(define bidi-move-marks ((shown bidi-shown-char-listp)
                         (pending bidi-shown-char-listp)
                         (ver versionp))
  :returns (new-shown bidi-shown-char-listp)
  :short "Rule L3: put the combining marks at right-to-left levels
          after their base characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first argument is a list of characters with their levels,
     in the order of display that rule L2 gives.
     There, text at an odd level is in the opposite order
     to the stored one,
     so the combining marks of a character come before it:
     a base with the marks m1 and m2, stored in that order,
     is displayed as m2, m1, base.
     This function puts it back as base, m1, m2.")
   (xdoc::p
    "It goes through the list and sets aside each combining mark
     at an odd level, as long as the marks set aside are at one level.
     The second argument is the list of the marks set aside,
     the last one first, which is the order in which they are stored;
     it is empty at the start.
     When the next character is not a mark
     and is at the level of the marks set aside, it is their base:
     it is put out first, and the marks after it.
     When the next character is anything else, or there is none,
     the marks set aside have no base next to them:
     they are put out in the order in which they are stored too.
     See @(see bidi-displayed-text) for what the specifications say."))
  (b* (((when (endp shown)) (bidi-shown-char-list-fix pending))
       (pending (bidi-shown-char-list-fix pending))
       ((bidi-shown-char char) (bidi-shown-char-fix (car shown)))
       (mark (and (oddp char.level)
                  (bidi-combining-mark-p char.code-point ver)))
       (same (and (consp pending)
                  (equal (bidi-shown-char->level (car pending))
                         char.level)))
       ((when (and mark
                   (or (endp pending)
                       same)))
        (bidi-move-marks (cdr shown) (cons char pending) ver))
       ((when mark)
        (append pending
                (bidi-move-marks (cdr shown) (list char) ver)))
       ((when same)
        (cons char
              (append pending
                      (bidi-move-marks (cdr shown) nil ver)))))
    (append pending
            (cons char
                  (bidi-move-marks (cdr shown) nil ver))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-mirror-char ((char bidi-shown-char-p) (ver versionp))
  :returns (cp code-point-p)
  :short "Rule L4 for one character: its mirroring glyph
          if it is at an odd level and has one, itself otherwise."
  :long
  (xdoc::topstring
   (xdoc::p
    "A character is drawn as its mirror image
     when it is at a right-to-left level
     and has the property @('Bidi_Mirrored') [UAX #9, rule L4].
     Every character with a @('Bidi_Mirroring_Glyph')
     has @('Bidi_Mirrored'),
     which the tool that generates the tables checks,
     so the test here is that the character has a mirroring glyph."))
  (b* (((bidi-shown-char char))
       (glyph? (code-point-bidi-mirroring-glyph char.code-point ver)))
    (if (and (oddp char.level)
             glyph?)
        (code-point-fix glyph?)
      char.code-point))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-mirror-chars ((shown bidi-shown-char-listp) (ver versionp))
  :returns (cps code-point-listp)
  :short "Rule L4 for a list of characters with their levels."
  (if (endp shown)
      nil
    (cons (bidi-mirror-char (car shown) ver)
          (bidi-mirror-chars (cdr shown) ver)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrulel bidi-level-option-listp-when-nat-listp
  (implies (nat-listp x)
           (bidi-level-option-listp x))
  :induct t
  :enable (bidi-level-option-listp nat-listp acl2::maybe-natp))

(define bidi-arrange-paragraph ((cps code-point-listp)
                                (direction paragraph-direction-p)
                                (ver versionp))
  :returns (shown bidi-shown-char-listp)
  :short "The characters of one paragraph in the order of display,
          each with its level."
  :long
  (xdoc::topstring
   (xdoc::p
    "The code points of the paragraph get their levels
     (see @(tsee bidi-paragraph-all-levels)),
     rule L2 puts them in the order of display
     (see @(tsee bidi-order-of-levels)),
     and rule L3 moves the combining marks
     (see @(tsee bidi-move-marks))."))
  (b* ((chars (code-points-to-bidi-chars cps ver))
       (paragraph-level (bidi-paragraph-embedding-level chars direction))
       (levels (bidi-paragraph-all-levels chars paragraph-level))
       (order (bidi-order-of-levels levels))
       (shown (bidi-shown-chars-at order (bidi-shown-chars cps levels))))
    (bidi-move-marks shown nil ver))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(defrulel code-points-to-bidi-chars-under-iff
  (iff (code-points-to-bidi-chars cps ver)
       (consp cps))
  :expand ((code-points-to-bidi-chars cps ver)))

(defrulel consp-of-code-points-to-bidi-chars
  (equal (consp (code-points-to-bidi-chars cps ver))
         (consp cps))
  :expand ((code-points-to-bidi-chars cps ver)))

(define bidi-arrange ((cps code-point-listp)
                      (direction paragraph-direction-p)
                      (ver versionp))
  :returns (shown bidi-shown-char-listp)
  :short "The characters of a list of code points in the order of display,
          each with its level, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The text is cut into paragraphs [UAX #9, rule P1],
     and the result is the paragraphs one after the other,
     each from left to right as it is displayed
     (see @(tsee bidi-arrange-paragraph)).
     This is the text after rules L2 and L3, which only move characters:
     the result has the code points of the argument, in another order
     (see @(see bidi-display-theorems))."))
  (b* (((when (endp cps)) nil)
       (cps (code-point-list-fix cps))
       (length (bidi-paragraph-length (code-points-to-bidi-chars cps ver))))
    (append (bidi-arrange-paragraph (take length cps) direction ver)
            (bidi-arrange (nthcdr length cps) direction ver)))
  :measure (len cps)
  :hints (("Goal"
           :in-theory (enable len nfix fix natp o-p o-finp o<)
           :use (:instance bidi-paragraph-length-lower-bound
                           (chars (code-points-to-bidi-chars
                                   (code-point-list-fix cps)
                                   ver)))))
  :guard-hints (("Goal"
                 :in-theory (enable nfix)
                 :use (:instance bidi-paragraph-length-upper-bound
                                 (chars (code-points-to-bidi-chars
                                         (code-point-list-fix cps)
                                         ver)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define bidi-display ((cps code-point-listp)
                      (direction paragraph-direction-p)
                      (ver versionp))
  :returns (displayed code-point-listp)
  :short "A list of code points as it is displayed,
          with every character kept, in a version of Unicode."
  :long
  (xdoc::topstring
   (xdoc::p
    "The characters are put in the order of display
     (see @(tsee bidi-arrange)),
     and rule L4 replaces the mirrored ones
     (see @(tsee bidi-mirror-char)).
     This is the string that the definition of the bidirectional skeleton
     in [UTS #39, Section 4] reaches
     after its three steps of reordering,
     before it takes the internal skeleton.")
   (xdoc::p
    "The result has as many code points as the argument.
     It is the argument in another order,
     except that a code point at an odd level that has a mirroring glyph
     is replaced by that glyph.
     See @(see bidi-display-theorems)."))
  (bidi-mirror-chars (bidi-arrange cps direction ver) ver)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-display-theorems
  :short "The text as displayed has the code points of the text as stored,
          in another order, before rule L4 replaces some of them."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rules L2 and L3 only move characters.
     So the list that @(tsee bidi-arrange) gives
     is a rearrangement of the argument:
     its code points are a permutation of the code points of the argument,
     which is the relation @('perm') of the ACL2 library
     @('[books]/kestrel/lists-light').
     In particular no character is lost,
     the characters that rule X9 removes included.
     Rule L4 then replaces a character by another one, in place,
     so @(tsee bidi-display) keeps the length.")
   (xdoc::p
    "The proof uses the theorem that
     the order that rule L2 gives is a permutation of the positions
     (see @(see bidi-rearrangement-theorems)).
     Here every character has a level,
     so those are all the positions of the paragraph."))

  ;; The characters at all the positions of a list are the list.

  (defrulel bidi-shown-chars-at-of-bidi-positions-with-level-when-posp
    (implies (and (posp position)
                  (nat-listp levels)
                  (consp shown))
             (equal (bidi-shown-chars-at
                     (bidi-positions-with-level levels position)
                     shown)
                    (bidi-shown-chars-at
                     (bidi-positions-with-level levels (- position 1))
                     (cdr shown))))
    :induct (bidi-positions-with-level levels position)
    :enable (bidi-positions-with-level
             bidi-shown-chars-at
             bidi-shown-char-at
             nfix
             posp))

  (local
   (defun two-lists-induction (x y)
     (if (or (atom x)
             (atom y))
         nil
       (two-lists-induction (cdr x) (cdr y)))))

  (defruled bidi-shown-chars-at-of-bidi-positions-with-level
    (implies (and (nat-listp levels)
                  (equal (len levels) (len shown)))
             (equal (bidi-shown-chars-at (bidi-positions-with-level levels 0)
                                         shown)
                    (bidi-shown-char-list-fix shown)))
    :induct (two-lists-induction levels shown)
    :enable (bidi-shown-chars-at
             bidi-shown-char-at
             bidi-shown-char-list-fix
             len
             fix)
    :expand ((bidi-positions-with-level levels 0)))

  ;; A paragraph and the rest of the text make the text.

  (local
   (defun position-and-list-induction (n x)
     (if (or (zp n) (atom x))
         nil
       (position-and-list-induction (- n 1) (cdr x)))))

  (defruled append-of-take-and-nthcdr-of-code-point-list-fix
    (implies (and (natp n)
                  (<= n (len cps)))
             (equal (append (take n (code-point-list-fix cps))
                            (code-point-list-fix (nthcdr n cps)))
                    (code-point-list-fix cps)))
    :induct (position-and-list-induction n cps)
    :enable (code-point-list-fix take nthcdr len natp fix))

  ;; Lengths.

  (defrulel len-of-bidi-positions-with-level-when-nat-listp
    (implies (nat-listp levels)
             (equal (len (bidi-positions-with-level levels position))
                    (len levels)))
    :induct (bidi-positions-with-level levels position)
    :enable (bidi-positions-with-level len nat-listp))

  (defrulel len-when-perm
    (implies (acl2::perm x x-equiv)
             (equal (len x) (len x-equiv)))
    :rule-classes :congruence
    :enable acl2::not-perm-when-not-equal-of-len-and-len)

  (defrulel len-of-bidi-order-of-levels-when-nat-listp
    (implies (nat-listp levels)
             (equal (len (bidi-order-of-levels levels))
                    (len levels))))

  (defrulel len-of-bidi-shown-chars-at
    (equal (len (bidi-shown-chars-at positions shown))
           (len positions))
    :induct t
    :enable (bidi-shown-chars-at len))

  (defrulel len-of-bidi-move-marks
    (implies (true-listp pending)
             (equal (len (bidi-move-marks shown pending ver))
                    (+ (len pending) (len shown))))
    :induct t
    :enable (bidi-move-marks len fix))

  (defrulel len-of-bidi-mirror-chars
    (equal (len (bidi-mirror-chars shown ver))
           (len shown))
    :induct t
    :enable (bidi-mirror-chars len))

  (defrulel len-of-bidi-arrange-paragraph
    (equal (len (bidi-arrange-paragraph cps direction ver))
           (len cps))
    :enable (bidi-arrange-paragraph fix))

  (defrule len-of-bidi-arrange
    (equal (len (bidi-arrange cps direction ver))
           (len cps))
    :induct t
    :enable (bidi-arrange nfix fix))

  (defrule len-of-bidi-display
    (equal (len (bidi-display cps direction ver))
           (len cps))
    :enable bidi-display)

  ;; Permutations.

  (defrulel perm-of-cons-and-cons-same
    (equal (acl2::perm (cons a x) (cons a y))
           (acl2::perm x y))
    :enable remove1-equal)

  (defrulel perm-of-cons-when-perm
    (implies (acl2::perm x x-equiv)
             (acl2::perm (cons a x) (cons a x-equiv)))
    :rule-classes :congruence)

  (defrulel perm-of-cons-of-cons
    (acl2::perm (cons a (cons b x))
                (cons b (cons a x)))
    :enable remove1-equal)

  (defruledl bidi-shown-chars-at-when-member-equal
    (implies (member-equal a positions)
             (acl2::perm (bidi-shown-chars-at positions shown)
                         (cons (bidi-shown-char-at a shown)
                               (bidi-shown-chars-at
                                (remove1-equal a positions)
                                shown))))
    :induct (bidi-shown-chars-at positions shown)
    :enable (bidi-shown-chars-at member-equal remove1-equal)
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2))

  (defrulel perm-of-bidi-shown-chars-at-when-perm
    (implies (acl2::perm positions positions-equiv)
             (acl2::perm (bidi-shown-chars-at positions shown)
                         (bidi-shown-chars-at positions-equiv shown)))
    :rule-classes :congruence
    :induct (acl2::perm positions positions-equiv)
    :enable (acl2::perm
             bidi-shown-chars-at
             bidi-shown-chars-at-when-member-equal)
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2))

  (defruledl bidi-shown-char-list-code-points-when-member-equal
    (implies (member-equal a shown)
             (acl2::perm (bidi-shown-char-list-code-points shown)
                         (cons (bidi-shown-char->code-point a)
                               (bidi-shown-char-list-code-points
                                (remove1-equal a shown)))))
    :induct (bidi-shown-char-list-code-points shown)
    :enable (bidi-shown-char-list-code-points member-equal remove1-equal)
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2))

  (defrulel perm-of-bidi-shown-char-list-code-points-when-perm
    (implies (acl2::perm shown shown-equiv)
             (acl2::perm (bidi-shown-char-list-code-points shown)
                         (bidi-shown-char-list-code-points shown-equiv)))
    :rule-classes :congruence
    :induct (acl2::perm shown shown-equiv)
    :enable (acl2::perm
             bidi-shown-char-list-code-points
             bidi-shown-char-list-code-points-when-member-equal)
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2))

  (defrulel perm-of-bidi-move-marks
    (implies (true-listp pending)
             (acl2::perm (bidi-move-marks shown pending ver)
                         (append (bidi-shown-char-list-fix pending)
                                 (bidi-shown-char-list-fix shown))))
    :induct (bidi-move-marks shown pending ver)
    :enable bidi-move-marks
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2
              acl2::perm-of-append))

  (defrulel perm-of-bidi-arrange-paragraph
    (acl2::perm (bidi-shown-char-list-code-points
                 (bidi-arrange-paragraph cps direction ver))
                (code-point-list-fix cps))
    :enable (bidi-arrange-paragraph
             bidi-shown-chars-at-of-bidi-positions-with-level))

  (defrule perm-of-bidi-arrange
    (acl2::perm (bidi-shown-char-list-code-points
                 (bidi-arrange cps direction ver))
                (code-point-list-fix cps))
    :induct (bidi-arrange cps direction ver)
    :enable (bidi-arrange
             nfix
             append-of-take-and-nthcdr-of-code-point-list-fix)
    :disable (acl2::perm-of-cons-arg1
              acl2::perm-of-cons-arg2
              acl2::perm-of-append))

  ;; Scalar values.

  (defrulel scalar-value-listp-of-code-points-of-bidi-arrange
    (implies (scalar-value-listp cps)
             (scalar-value-listp (bidi-shown-char-list-code-points
                                  (bidi-arrange cps direction ver))))
    :use (:instance scalar-value-listp-when-subsetp-equal
                    (acl2::x (bidi-shown-char-list-code-points
                              (bidi-arrange cps direction ver)))
                    (acl2::y cps)))

  (defrulel scalar-value-listp-of-bidi-mirror-chars
    (implies (scalar-value-listp (bidi-shown-char-list-code-points shown))
             (scalar-value-listp (bidi-mirror-chars shown ver)))
    :induct (bidi-mirror-chars shown ver)
    :enable (bidi-mirror-chars
             bidi-mirror-char
             bidi-shown-char-list-code-points))

  (defrule scalar-value-listp-of-bidi-display
    (implies (scalar-value-listp cps)
             (scalar-value-listp (bidi-display cps direction ver)))
    :enable bidi-display))
