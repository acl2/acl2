; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-display")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book is a step of the proofs of the theorems of the books
; bidi-guarded-theorem.lisp and bidi-self-contained.lisp.
; Those books include this one locally,
; through the book bidi-guarded-neutral.lisp.
; See each of the two books for the outline of its proof.
; The books bidi-rule-display-levels.lisp
; and bidi-rule-left-to-right-label.lisp include it locally too,
; for the theorem about a paragraph embedding level that is given here.
;
; A class is plain if it is not B (Paragraph Separator),
; not one of the classes that rule X9 of the Unicode Bidirectional Algorithm
; removes, and not the class of an isolate formatting character.
; A paragraph whose characters all have plain classes
; has no embedding, no override and no isolate.
; So, at any paragraph embedding level:
; rules X1 to X8 give every character that level and leave the classes;
; rule X9 removes nothing;
; the whole paragraph is one isolating run sequence,
; with sos and eos in the direction of that level;
; and so the levels before rule L1 are the result
; of one call of BIDI-RESOLVE-SEQUENCE
; (theorem BIDI-PARAGRAPH-ALL-LEVELS-WHEN-PLAIN-AT-LEVEL).
; At the level 0, sos = eos = L, and rule L1 only changes some levels to 0.
;
; This book proves the consequence that the first proof needs:
; if some positions have level 0 in the result of that one call,
; they have level 0 in the result of BIDI-PARAGRAPH-ALL-LEVELS.
; The positions are given by a list of booleans, called OUTSIDE,
; that goes along the list of the levels:
; see the book bidi-guarded-theorem.lisp for the reason for the name.
;
; The second proof needs to know what rule L1 does exactly.
; This book defines BIDI-RESET-PLAIN, which is the rule
; for plain classes at the paragraph embedding level 0, and proves that
; the levels of the paragraph are its result on the levels
; that the one call gives.  It also proves that the function
; does to the part of a list from a position on,
; and under a condition to the part of a list up to a position,
; what it does to that part alone.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definitions that the other books of the proofs use.

(define bidi-plain-class-p ((class bidi-class-p))
  :returns (yes/no booleanp)
  (not (or (equal (bidi-class-kind class) :paragraph-separator)
           (bidi-class-removed-p class)
           (bidi-class-isolate-formatting-p class)))
  :hooks (:fix))

(std::deflist bidi-plain-class-listp (x)
  :guard (bidi-class-listp x)
  (bidi-plain-class-p x))

; Every position for which OUTSIDE has T has level 0.

(define bidi-outside-zero-p ((outside boolean-listp) (levels nat-listp))
  :returns (yes/no booleanp)
  (or (endp levels)
      (and (or (not (car outside))
               (equal (lnfix (car levels)) 0))
           (bidi-outside-zero-p (cdr outside) (cdr levels))))
  :measure (acl2-count levels)
  :hooks nil)

; Rule L1 for plain classes at the paragraph embedding level 0,
; as a function of the classes and the levels.
; The second result says whether the list is white space
; up to a segment separator or up to its end.

(define bidi-reset-plain ((classes bidi-class-listp) (levels nat-listp))
  :returns (mv (new-levels nat-listp)
               (trailing booleanp))
  (b* (((when (or (endp classes)
                  (endp levels)))
        (mv nil t))
       ((mv rest trailing) (bidi-reset-plain (cdr classes) (cdr levels)))
       (kind (bidi-class-kind (car classes)))
       (level (lnfix (car levels))))
    (cond ((eq kind :segment-separator) (mv (cons 0 rest) t))
          ((eq kind :white-space) (mv (cons (if trailing 0 level) rest)
                                      trailing))
          (t (mv (cons level rest) nil))))
  :hooks nil)

; Every class of the list is WS.

(define bidi-all-white-p ((classes bidi-class-listp))
  :returns (yes/no booleanp)
  (or (endp classes)
      (and (equal (bidi-class-kind (car classes)) :white-space)
           (bidi-all-white-p (cdr classes))))
  :hooks nil)

; The white space at the end of the list has the level 0.

(define bidi-trailing-zero-p ((classes bidi-class-listp) (levels nat-listp))
  :returns (yes/no booleanp)
  (or (endp classes)
      (and (or (not (bidi-all-white-p classes))
               (equal (nfix (car levels)) 0))
           (bidi-trailing-zero-p (cdr classes) (cdr levels))))
  :verify-guards nil
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; From here to the last theorem, the events are local.

(local
 (define list-induction (x)
   (if (consp x)
       (list-induction (cdr x))
     nil)
   :hooks nil))

(local
 (define two-lists-induction (x y)
   (if (and (consp x)
            (consp y))
       (two-lists-induction (cdr x) (cdr y))
     nil)
   :hooks nil))

(local
 (define three-lists-induction (x y z)
   (if (and (consp y)
            (consp z))
       (three-lists-induction (cdr x) (cdr y) (cdr z))
     nil)
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel fix-of-len
  (equal (fix (len x))
         (len x))
  :enable fix)

(defrulel nfix-of-+-of-1-and-len
  (equal (nfix (+ 1 (len x)))
         (+ 1 (len x)))
  :enable nfix)

(defrulel bidi-outside-zero-p-of-nil
  (bidi-outside-zero-p nil levels)
  :induct (list-induction levels)
  :enable (list-induction bidi-outside-zero-p))

(defrulel bidi-outside-zero-p-when-not-consp
  (implies (not (consp outside))
           (bidi-outside-zero-p outside levels))
  :expand (bidi-outside-zero-p outside levels)
  :enable (acl2::default-car acl2::default-cdr))

(defrulel bidi-outside-zero-p-of-nat-list-fix
  (equal (bidi-outside-zero-p outside (nat-list-fix levels))
         (bidi-outside-zero-p outside levels))
  :induct (bidi-outside-zero-p outside levels)
  :enable (bidi-outside-zero-p nat-list-fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The characters with their levels and classes after rules X1 to X8,
; when the classes are plain:
; every level is the paragraph embedding level
; and the class is the one that the character has.

(local
 (define flat-lchars ((chars bidi-char-listp) (level natp))
   :returns (lchars bidi-leveled-char-listp)
   (b* (((when (endp chars)) nil)
        ((bidi-char char) (car chars)))
     (cons (make-bidi-leveled-char :original char.class
                                   :class char.class
                                   :bracket char.bracket
                                   :level level)
           (flat-lchars (cdr chars) level)))
   :hooks nil
   ///
   (defret len-of-flat-lchars
     (equal (len lchars)
            (len chars))
     :hints (("Goal" :induct t :in-theory (enable len))))))

(defrulel flat-lchars-of-nfix
  (equal (flat-lchars chars (nfix level))
         (flat-lchars chars level))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars))

(defrulel bidi-leveled-char-list-classes-of-flat-lchars
  (equal (bidi-leveled-char-list-classes (flat-lchars chars level))
         (bidi-char-list-classes chars))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-classes
           bidi-leveled-char-list-classes))

(defrulel bidi-leveled-char-list-brackets-of-flat-lchars
  (equal (bidi-leveled-char-list-brackets (flat-lchars chars level))
         (bidi-char-list-brackets chars))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-brackets
           bidi-leveled-char-list-brackets))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules X1 to X8.

(defrulel bidi-explicit-step-when-plain
  (implies (and (bidi-plain-class-p class)
                (equal (directional-override-kind
                        (directional-status->override
                         (explicit-state->top st)))
                       :neutral))
           (equal (bidi-explicit-step class rest st paragraph-level)
                  (mv (directional-status->level (explicit-state->top st))
                      (bidi-class-fix class)
                      (explicit-state-fix st))))
  :enable (bidi-explicit-step
           bidi-plain-class-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p
           apply-directional-override))

(defrulel bidi-leveled-chars-of-bidi-explicit-levels-from-when-plain
  (implies (and (bidi-plain-class-listp (bidi-char-list-classes chars))
                (equal (directional-override-kind
                        (directional-status->override
                         (explicit-state->top st)))
                       :neutral))
           (b* (((mv levels classes)
                 (bidi-explicit-levels-from (bidi-char-list-classes chars)
                                            st
                                            paragraph-level)))
             (equal (bidi-leveled-chars chars levels classes)
                    (flat-lchars chars
                                 (directional-status->level
                                  (explicit-state->top st))))))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-classes
           bidi-leveled-chars
           bidi-explicit-levels-from))

; Rule X9.

(defrulel bidi-remove-by-x9-of-flat-lchars
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (equal (bidi-remove-by-x9 (flat-lchars chars level))
                  (flat-lchars chars level)))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-classes
           bidi-remove-by-x9
           bidi-plain-class-p))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The isolating run sequences: there is one, and it has every position.

(local
 (define nat-range ((start natp) (end natp))
   :returns (positions nat-listp)
   (b* ((start (lnfix start))
        (end (lnfix end)))
     (if (>= start end)
         nil
       (cons start
             (nat-range (+ 1 start) end))))
   :measure (nfix (- (nfix end) (nfix start)))
   :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
   :hooks nil))

(local
 (define char-at-induction (position chars)
   (if (or (zp position)
           (atom chars))
       nil
     (char-at-induction (- position 1) (cdr chars)))
   :verify-guards nil
   :hooks nil))

(local
 (define up-to-induction (position n)
   (if (< (nfix position) (nfix n))
       (up-to-induction (+ 1 (nfix position)) n)
     nil)
   :measure (nfix (- (nfix n) (nfix position)))
   :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
   :verify-guards nil
   :hooks nil))

(defrulel bidi-leveled-char->level-of-bidi-leveled-char-at-of-flat-lchars
  (implies (< (nfix position) (len chars))
           (equal (bidi-leveled-char->level
                   (bidi-leveled-char-at position (flat-lchars chars level)))
                  (nfix level)))
  :induct (char-at-induction position chars)
  :enable (char-at-induction
           len
           nfix)
  :expand ((flat-lchars chars level)
           (:free (a b) (bidi-leveled-char-at position (cons a b)))))

(defrulel bidi-leveled-char->original-of-bidi-leveled-char-at-of-flat-lchars
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (bidi-plain-class-p
            (bidi-leveled-char->original
             (bidi-leveled-char-at position (flat-lchars chars level)))))
  :induct (char-at-induction position chars)
  :enable (char-at-induction
           bidi-char-list-classes
           nfix)
  :expand ((flat-lchars chars level)
           (:free (a b) (bidi-leveled-char-at position (cons a b)))
           (bidi-leveled-char-at position nil)))

(defrulel not-isolate-when-bidi-plain-class-p
  (implies (bidi-plain-class-p class)
           (and (not (bidi-class-isolate-initiator-p class))
                (not (equal (bidi-class-kind class)
                            :pop-directional-isolate))))
  :enable (bidi-plain-class-p
           bidi-class-isolate-formatting-p))

(defrulel bidi-sequence-successor-of-flat-lchars
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (equal (bidi-sequence-successor position (flat-lchars chars level))
                  (and (< (+ 1 (nfix position)) (len chars))
                       (+ 1 (nfix position)))))
  :enable (bidi-sequence-successor
           nfix
           natp))

(defrulel nat-range-when-not-below
  (implies (<= (nfix end) (nfix start))
           (equal (nat-range start end)
                  nil))
  :expand (nat-range start end)
  :enable nfix)

(defrulel bidi-sequence-from-of-flat-lchars
  (implies (and (bidi-plain-class-listp (bidi-char-list-classes chars))
                (equal n (len chars)))
           (equal (bidi-sequence-from position (flat-lchars chars level))
                  (nat-range position n)))
  :induct (up-to-induction position n)
  :enable (up-to-induction
           nfix
           natp)
  :expand ((bidi-sequence-from position (flat-lchars chars level))
           (:free (m) (nat-range position m))))

(defrulel bidi-sequence-start-p-of-flat-lchars
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (equal (bidi-sequence-start-p position (flat-lchars chars level))
                  (and (< (nfix position) (len chars))
                       (equal (nfix position) 0))))
  :enable (bidi-sequence-start-p
           nfix
           natp))

(defrulel bidi-level-at-of-flat-lchars
  (equal (bidi-level-at position (flat-lchars chars level) level)
         (nfix level))
  :enable bidi-level-at)

; The characters at all the positions are all the characters.

(defruledl bidi-leveled-chars-at-of-nat-range-of-next
  (implies (and (natp start)
                (natp end)
                (consp lchars))
           (equal (bidi-leveled-chars-at (nat-range (+ 1 start) (+ 1 end))
                                         lchars)
                  (bidi-leveled-chars-at (nat-range start end)
                                         (cdr lchars))))
  :induct (nat-range start end)
  :expand (nat-range (+ 1 start) (+ 1 end))
  :enable (nat-range
           bidi-leveled-chars-at
           bidi-leveled-char-at
           nfix
           fix
           natp))

(defrulel bidi-leveled-chars-at-of-nat-range-of-1
  (implies (and (natp end)
                (consp lchars))
           (equal (bidi-leveled-chars-at (nat-range 1 (+ 1 end)) lchars)
                  (bidi-leveled-chars-at (nat-range 0 end) (cdr lchars))))
  :use (:instance bidi-leveled-chars-at-of-nat-range-of-next (start 0)))

(defrulel bidi-leveled-chars-at-of-nat-range-of-all
  (equal (bidi-leveled-chars-at (nat-range 0 (len lchars)) lchars)
         (bidi-leveled-char-list-fix lchars))
  :induct (list-induction lchars)
  :enable (list-induction
           len
           bidi-leveled-chars-at
           bidi-leveled-char-at)
  :expand (nat-range 0 (+ 1 (len (cdr lchars)))))

; The levels put at all the positions are all the new levels.

(local
 (define set-range-induction ((start natp) (end natp) values levels)
   (b* ((start (nfix start))
        (end (nfix end)))
     (if (or (>= start end)
             (not (consp values)))
         nil
       (set-range-induction (+ 1 start)
                            end
                            (cdr values)
                            (cons (nfix (car levels))
                                  (nat-list-set start
                                                (car values)
                                                (cdr levels))))))
   :measure (nfix (- (nfix end) (nfix start)))
   :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defruledl nat-list-set-list-of-nat-range-of-next
  (implies (and (natp start)
                (natp end)
                (consp levels))
           (equal (nat-list-set-list (nat-range (+ 1 start) (+ 1 end))
                                     values
                                     levels)
                  (cons (nfix (car levels))
                        (nat-list-set-list (nat-range start end)
                                           values
                                           (cdr levels)))))
  :induct (set-range-induction start end values levels)
  :expand (nat-range (+ 1 start) (+ 1 end))
  :enable (set-range-induction
           nat-range
           nat-list-set-list
           nat-list-set
           nfix
           fix
           natp))

(defrulel nat-list-set-list-of-nat-range-of-1
  (implies (and (natp end)
                (consp levels))
           (equal (nat-list-set-list (nat-range 1 (+ 1 end)) values levels)
                  (cons (nfix (car levels))
                        (nat-list-set-list (nat-range 0 end)
                                           values
                                           (cdr levels)))))
  :use (:instance nat-list-set-list-of-nat-range-of-next (start 0)))

(defruledl nat-list-set-list-of-nat-range-of-all-lemma
  (implies (equal (len values) (len levels))
           (equal (nat-list-set-list (nat-range 0 (len levels))
                                     values
                                     levels)
                  (nat-list-fix values)))
  :induct (two-lists-induction values levels)
  :enable (two-lists-induction
           len
           nat-list-fix
           nat-list-set-list
           nat-list-set)
  :expand (nat-range 0 (+ 1 (len (cdr levels)))))

(defrulel nat-list-set-list-of-nat-range-of-all
  (implies (and (equal (len values) end)
                (equal (len levels) end))
           (equal (nat-list-set-list (nat-range 0 end) values levels)
                  (nat-list-fix values)))
  :enable nat-list-set-list-of-nat-range-of-all-lemma)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rules X10, W1 to W7, N0 to N2, I1 and I2:
; one call of BIDI-RESOLVE-SEQUENCE,
; with sos and eos in the direction of the paragraph embedding level.

(defrulel nfix-of-nat-list-last
  (equal (nfix (nat-list-last positions))
         (nat-list-last positions))
  :enable nfix)

(defrulel bidi-resolve-sequence-at-of-flat-lchars
  (implies (and (bidi-plain-class-listp (bidi-char-list-classes chars))
                (consp positions)
                (< (nfix (car positions)) (len chars))
                (< (nat-list-last positions) (len chars)))
           (equal (bidi-resolve-sequence-at positions
                                            (flat-lchars chars level)
                                            level)
                  (b* ((sequence (bidi-leveled-chars-at
                                  positions
                                  (flat-lchars chars level))))
                    (bidi-resolve-sequence
                     (bidi-leveled-char-list-classes sequence)
                     (bidi-leveled-char-list-brackets sequence)
                     (bidi-level-direction level)
                     (bidi-level-direction level)
                     level))))
  :enable (bidi-resolve-sequence-at
           max))

(defrulel bidi-resolve-sequences-from-of-flat-lchars-and-not-first
  (implies (and (bidi-plain-class-listp (bidi-char-list-classes chars))
                (equal n (len chars))
                (natp position)
                (< 0 position))
           (equal (bidi-resolve-sequences-from position
                                               (flat-lchars chars level)
                                               level
                                               levels)
                  (nat-list-fix levels)))
  :induct (up-to-induction position n)
  :enable (up-to-induction
           nfix
           natp)
  :expand ((bidi-resolve-sequences-from position
                                        (flat-lchars chars level)
                                        level
                                        levels)))

(defrulel consp-of-nat-range-of-0
  (implies (consp x)
           (consp (nat-range 0 (len x))))
  :expand ((len x)
           (nat-range 0 (+ 1 (len (cdr x))))))

(defrulel car-of-nat-range-of-0
  (implies (consp x)
           (equal (car (nat-range 0 (len x)))
                  0))
  :expand ((len x)
           (nat-range 0 (+ 1 (len (cdr x))))))

(defrulel nat-list-last-of-nat-range-upper-bound
  (implies (and (natp start)
                (natp end)
                (< start end))
           (< (nat-list-last (nat-range start end)) end))
  :rule-classes :linear
  :induct (nat-range start end)
  :enable (nat-range
           nat-list-last
           nfix))

(defrulel nat-list-last-of-nat-range-of-0
  (implies (consp x)
           (< (nat-list-last (nat-range 0 (len x))) (len x)))
  :enable len)

(defrulel bidi-leveled-chars-at-of-nat-range-of-all-of-flat-lchars
  (equal (bidi-leveled-chars-at (nat-range 0 (len chars))
                                (flat-lchars chars level))
         (flat-lchars chars level))
  :use (:instance bidi-leveled-chars-at-of-nat-range-of-all
                  (lchars (flat-lchars chars level)))
  :disable bidi-leveled-chars-at-of-nat-range-of-all)

(defrulel bidi-resolve-sequences-from-of-flat-lchars
  (implies (and (bidi-plain-class-listp (bidi-char-list-classes chars))
                (equal (len levels) (len chars)))
           (equal (bidi-resolve-sequences-from 0
                                               (flat-lchars chars level)
                                               level
                                               levels)
                  (if (consp chars)
                      (bidi-resolve-sequence
                       (bidi-char-list-classes chars)
                       (bidi-char-list-brackets chars)
                       (bidi-level-direction level)
                       (bidi-level-direction level)
                       level)
                    (nat-list-fix levels))))
  :expand (bidi-resolve-sequences-from 0
                                       (flat-lchars chars level)
                                       level
                                       levels)
  :enable len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L1 keeps the length of the list of the levels.
; With plain classes rule X9 removes no character,
; so giving the removed characters a level changes nothing.

(defrulel len-of-bidi-reset-levels
  (implies (equal (len levels) (len lchars))
           (equal (len (mv-nth 0 (bidi-reset-levels lchars levels level)))
                  (len lchars)))
  :induct (two-lists-induction lchars levels)
  :enable (two-lists-induction
           bidi-reset-levels
           len))

(local
 (define fill-induction (originals levels previous)
   (if (and (consp originals)
            (consp levels))
       (fill-induction (cdr originals) (cdr levels) (nfix (car levels)))
     previous)
   :irrelevant-formals-ok t
   :verify-guards nil
   :hooks nil))

(defrulel bidi-fill-levels-of-bidi-expand-levels-when-plain
  (implies (and (bidi-plain-class-listp originals)
                (nat-listp levels)
                (equal (len levels) (len originals)))
           (equal (bidi-fill-levels (bidi-expand-levels originals levels)
                                    previous)
                  levels))
  :induct (fill-induction originals levels previous)
  :enable (fill-induction
           bidi-fill-levels
           bidi-expand-levels
           bidi-plain-class-p
           len
           acl2::maybe-natp-fix
           nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L1 exactly, and on a part of the paragraph.
;
; For plain classes at the paragraph embedding level 0,
; rule L1, and the rule for all the characters, are BIDI-RESET-PLAIN;
; applied twice it does what it does once.
; So the levels of the paragraph are the result of BIDI-RESET-PLAIN
; on the levels that the one call of BIDI-RESOLVE-SEQUENCE gives.
;
; The rule goes from the end of the list to its start.
; So on the part of the list from a position on
; it does what it does to that part alone.
; On the part of the list up to a position it does the same too,
; if the white space at the end of that part has the level 0 already:
; the rule gives that white space the level 0 when the part is alone.

(defrulel bidi-reset-levels-of-flat-lchars
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (equal (bidi-reset-levels (flat-lchars chars level)
                                     levels
                                     paragraph-level)
                  (bidi-reset-all-levels (bidi-char-list-classes chars)
                                         levels
                                         paragraph-level)))
  :induct (two-lists-induction chars levels)
  :expand ((flat-lchars chars level)
           (bidi-char-list-classes chars)
           (:free (a b)
                  (bidi-reset-levels (cons a b) levels paragraph-level))
           (:free (a b)
                  (bidi-reset-all-levels (cons a b) levels paragraph-level))
           (bidi-reset-levels nil levels paragraph-level)
           (bidi-reset-all-levels nil levels paragraph-level)
           (:free (a b) (bidi-reset-levels (cons a b) nil paragraph-level))
           (:free (a b)
                  (bidi-reset-all-levels (cons a b) nil paragraph-level)))
  :enable (two-lists-induction
           bidi-plain-class-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

; Rule L1, done twice, does what it does once.

(local
 (define trailing-all-p ((classes bidi-class-listp))
   :returns (yes/no booleanp)
   (b* (((when (endp classes)) t)
        (class (bidi-class-fix (car classes))))
     (cond ((or (equal (bidi-class-kind class) :segment-separator)
                (equal (bidi-class-kind class) :paragraph-separator))
            t)
           ((or (equal (bidi-class-kind class) :white-space)
                (bidi-class-isolate-formatting-p class)
                (bidi-class-removed-p class))
            (trailing-all-p (cdr classes)))
           (t nil)))
   :hooks nil))

(defrulel trailing-of-bidi-reset-all-levels
  (implies (equal (len levels) (len classes))
           (equal (mv-nth 1 (bidi-reset-all-levels classes levels level))
                  (trailing-all-p classes)))
  :induct (two-lists-induction classes levels)
  :expand ((bidi-reset-all-levels classes levels level)
           (trailing-all-p classes))
  :enable (two-lists-induction len))

(defrulel bidi-reset-all-levels-of-bidi-reset-all-levels
  (implies (equal (len levels) (len classes))
           (equal (mv-nth 0 (bidi-reset-all-levels
                             classes
                             (mv-nth 0 (bidi-reset-all-levels classes
                                                              levels
                                                              level))
                             level))
                  (mv-nth 0 (bidi-reset-all-levels classes levels level))))
  :induct (two-lists-induction classes levels)
  :expand ((bidi-reset-all-levels classes levels level)
           (bidi-reset-all-levels classes nil level)
           (:free (a b) (bidi-reset-all-levels classes (cons a b) level)))
  :enable (two-lists-induction len))

(defrulel bidi-reset-all-levels-when-plain
  (implies (bidi-plain-class-listp classes)
           (equal (bidi-reset-all-levels classes levels 0)
                  (bidi-reset-plain classes levels)))
  :induct (two-lists-induction classes levels)
  :expand ((bidi-reset-all-levels classes levels 0)
           (bidi-reset-plain classes levels))
  :enable (two-lists-induction
           bidi-plain-class-p
           bidi-class-removed-p
           bidi-class-isolate-formatting-p
           bidi-class-isolate-initiator-p))

(defrulel bidi-reset-plain-when-not-consp
  (implies (or (not (consp classes))
               (not (consp levels)))
           (equal (bidi-reset-plain classes levels)
                  (mv nil t)))
  :expand (bidi-reset-plain classes levels))

(defrulel len-of-bidi-reset-plain
  (implies (equal (len levels) (len classes))
           (equal (len (mv-nth 0 (bidi-reset-plain classes levels)))
                  (len classes)))
  :induct (two-lists-induction classes levels)
  :expand (bidi-reset-plain classes levels)
  :enable (two-lists-induction len))

(defrulel bidi-outside-zero-p-of-bidi-reset-plain
  (implies (bidi-outside-zero-p outside levels)
           (bidi-outside-zero-p outside
                                (mv-nth 0 (bidi-reset-plain classes levels))))
  :induct (three-lists-induction outside levels classes)
  :expand ((bidi-reset-plain classes levels)
           (:free (a b) (bidi-outside-zero-p outside (cons a b))))
  :enable (three-lists-induction
           bidi-outside-zero-p))

; The second result depends on the classes only.

(local
 (define trailing-white-p ((classes bidi-class-listp))
   :returns (yes/no booleanp)
   (b* (((when (endp classes)) t)
        (kind (bidi-class-kind (car classes))))
     (cond ((eq kind :segment-separator) t)
           ((eq kind :white-space) (trailing-white-p (cdr classes)))
           (t nil)))
   :hooks nil))

(defrulel trailing-of-bidi-reset-plain
  (implies (equal (len levels) (len classes))
           (equal (mv-nth 1 (bidi-reset-plain classes levels))
                  (trailing-white-p classes)))
  :induct (two-lists-induction classes levels)
  :expand ((bidi-reset-plain classes levels)
           (trailing-white-p classes))
  :enable (two-lists-induction len))

(defrulel bidi-reset-plain-of-bidi-reset-plain
  (implies (equal (len levels) (len classes))
           (equal (mv-nth 0 (bidi-reset-plain
                             classes
                             (mv-nth 0 (bidi-reset-plain classes levels))))
                  (mv-nth 0 (bidi-reset-plain classes levels))))
  :induct (two-lists-induction classes levels)
  :expand ((bidi-reset-plain classes levels)
           (:free (a b) (bidi-reset-plain classes (cons a b))))
  :enable (two-lists-induction len))

; The part of the list from a position on.

(local
 (define nthcdr-two-induction ((k natp) x y)
   (if (or (zp k)
           (atom x)
           (atom y))
       nil
     (nthcdr-two-induction (- k 1) (cdr x) (cdr y)))
   :verify-guards nil
   :hooks nil))

; The part of the list up to a position.

(defrulel trailing-white-p-when-bidi-all-white-p
  (implies (bidi-all-white-p classes)
           (trailing-white-p classes))
  :induct (list-induction classes)
  :enable (list-induction bidi-all-white-p trailing-white-p))

(defrulel trailing-white-p-of-take
  (implies (and (trailing-white-p classes)
                (<= (nfix m) (len classes)))
           (trailing-white-p (take m classes)))
  :induct (nthcdr-two-induction m classes classes)
  :expand ((trailing-white-p classes)
           (:free (a b) (trailing-white-p (cons a b)))
           (trailing-white-p nil))
  :enable (nthcdr-two-induction take len nfix))

(defrulel bidi-all-white-p-of-take-when-trailing-white-p
  (implies (and (trailing-white-p (take m classes))
                (not (trailing-white-p classes))
                (<= (nfix m) (len classes)))
           (bidi-all-white-p (take m classes)))
  :induct (nthcdr-two-induction m classes classes)
  :expand ((trailing-white-p classes)
           (:free (a b) (trailing-white-p (cons a b)))
           (:free (a b) (bidi-all-white-p (cons a b)))
           (bidi-all-white-p nil))
  :enable (nthcdr-two-induction take len nfix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorems of this book.

(defrulel bidi-outside-zero-p-of-no-levels
  (bidi-outside-zero-p outside nil)
  :expand (bidi-outside-zero-p outside nil))

(defrulel bidi-reset-all-levels-of-nil
  (equal (mv-nth 0 (bidi-reset-all-levels nil levels level))
         nil)
  :expand (bidi-reset-all-levels nil levels level))

(defrulel flat-lchars-under-iff
  (iff (flat-lchars chars level)
       (consp chars))
  :expand (flat-lchars chars level))

(defrulel bidi-char-list-classes-when-not-consp
  (implies (not (consp chars))
           (equal (bidi-char-list-classes chars)
                  nil))
  :expand (bidi-char-list-classes chars))

; The levels of a plain paragraph, at any paragraph embedding level:
; one call of BIDI-RESOLVE-SEQUENCE, then rule L1.

(defruled bidi-paragraph-all-levels-when-plain-at-level
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (equal (bidi-paragraph-all-levels chars level)
                  (mv-nth 0 (bidi-reset-all-levels
                             (bidi-char-list-classes chars)
                             (bidi-resolve-sequence
                              (bidi-char-list-classes chars)
                              (bidi-char-list-brackets chars)
                              (bidi-level-direction level)
                              (bidi-level-direction level)
                              level)
                             level))))
  :enable (bidi-paragraph-all-levels
           bidi-paragraph-levels
           bidi-explicit-levels))

; The levels of a plain paragraph, at the paragraph embedding level 0.

(defruled bidi-paragraph-all-levels-when-plain
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (equal (bidi-paragraph-all-levels chars 0)
                  (mv-nth 0 (bidi-reset-plain
                             (bidi-char-list-classes chars)
                             (bidi-resolve-sequence
                              (bidi-char-list-classes chars)
                              (bidi-char-list-brackets chars)
                              (bidi-class-left-to-right)
                              (bidi-class-left-to-right)
                              0)))))
  :enable (bidi-paragraph-all-levels-when-plain-at-level
           bidi-level-direction))

(defrule bidi-outside-zero-p-of-bidi-paragraph-all-levels-when-plain
  (implies (and (bidi-plain-class-listp (bidi-char-list-classes chars))
                (bidi-outside-zero-p outside
                                     (bidi-resolve-sequence
                                      (bidi-char-list-classes chars)
                                      (bidi-char-list-brackets chars)
                                      (bidi-class-left-to-right)
                                      (bidi-class-left-to-right)
                                      0)))
           (bidi-outside-zero-p outside (bidi-paragraph-all-levels chars 0)))
  :enable bidi-paragraph-all-levels-when-plain)

; Rule L1 on a part of the paragraph.

(defruled nthcdr-of-bidi-reset-plain
  (equal (nthcdr k (mv-nth 0 (bidi-reset-plain classes levels)))
         (mv-nth 0 (bidi-reset-plain (nthcdr k classes) (nthcdr k levels))))
  :induct (nthcdr-two-induction k classes levels)
  :expand (bidi-reset-plain classes levels)
  :enable (nthcdr-two-induction nthcdr))

(defruled take-of-bidi-reset-plain
  (implies (and (equal (len levels) (len classes))
                (<= (nfix m) (len classes))
                (bidi-trailing-zero-p (take m classes) (take m levels)))
           (equal (take m (mv-nth 0 (bidi-reset-plain classes levels)))
                  (mv-nth 0 (bidi-reset-plain (take m classes)
                                              (take m levels)))))
  :induct (nthcdr-two-induction m classes levels)
  :expand ((bidi-reset-plain classes levels)
           (:free (a b c d) (bidi-reset-plain (cons a b) (cons c d)))
           (:free (a b c) (bidi-trailing-zero-p (cons a b) c))
           (:free (a b) (bidi-all-white-p (cons a b))))
  :enable (nthcdr-two-induction take len nfix))
