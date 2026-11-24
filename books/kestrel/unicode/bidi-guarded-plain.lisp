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

; This book is a step of the proof of the theorem of the book
; bidi-guarded-theorem.lisp.  That book includes this one locally,
; through the book bidi-guarded-neutral.lisp.
; See the book bidi-guarded-theorem.lisp for the plan of the proof.
;
; A class is plain if it is not B (Paragraph Separator),
; not one of the classes that rule X9 of the Unicode Bidirectional Algorithm
; removes, and not the class of an isolate formatting character.
; A paragraph whose characters all have plain classes
; has no embedding, no override and no isolate.
; So, when the paragraph embedding level is 0:
; rules X1 to X8 give every character the level 0 and leave the classes;
; rule X9 removes nothing;
; the whole paragraph is one isolating run sequence, with sos = eos = L;
; and so the levels before rule L1 are the result
; of one call of BIDI-RESOLVE-SEQUENCE.
; Rule L1 only changes some levels to 0.
;
; This book proves the consequence that the rest of the proof needs
; (the last theorem of this book):
; if some positions have level 0 in the result of that one call,
; they have level 0 in the result of BIDI-PARAGRAPH-ALL-LEVELS.
; The positions are given by a list of booleans, called OUTSIDE,
; that goes along the list of the levels:
; see the book bidi-guarded-theorem.lisp for the reason for the name.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The definitions that the other books of the proof use.

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
; when the classes are plain and the paragraph embedding level is 0:
; every level is 0 and the class is the one that the character has.

(local
 (define flat-lchars ((chars bidi-char-listp))
   :returns (lchars bidi-leveled-char-listp)
   (b* (((when (endp chars)) nil)
        ((bidi-char char) (car chars)))
     (cons (make-bidi-leveled-char :original char.class
                                   :class char.class
                                   :bracket char.bracket
                                   :level 0)
           (flat-lchars (cdr chars))))
   :hooks nil
   ///
   (defret len-of-flat-lchars
     (equal (len lchars)
            (len chars))
     :hints (("Goal" :induct t :in-theory (enable len))))))

; A character with level 0 and a plain class.

(local
 (define lchar-flat-p ((lchar bidi-leveled-char-p))
   :returns (yes/no booleanp)
   (and (equal (bidi-leveled-char->level lchar) 0)
        (bidi-plain-class-p (bidi-leveled-char->original lchar)))
   :hooks nil))

(local
 (std::deflist lchars-flat-p (x)
   :guard (bidi-leveled-char-listp x)
   (lchar-flat-p x)))

(defrulel lchars-flat-p-of-flat-lchars
  (implies (bidi-plain-class-listp (bidi-char-list-classes chars))
           (lchars-flat-p (flat-lchars chars)))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-classes
           lchar-flat-p))

(defrulel bidi-leveled-char-list-classes-of-flat-lchars
  (equal (bidi-leveled-char-list-classes (flat-lchars chars))
         (bidi-char-list-classes chars))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-classes
           bidi-leveled-char-list-classes))

(defrulel bidi-leveled-char-list-brackets-of-flat-lchars
  (equal (bidi-leveled-char-list-brackets (flat-lchars chars))
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
                (equal (directional-status->level (explicit-state->top st))
                       0)
                (equal (directional-override-kind
                        (directional-status->override
                         (explicit-state->top st)))
                       :neutral))
           (equal (bidi-explicit-step class rest st paragraph-level)
                  (mv 0
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
                (equal (directional-status->level (explicit-state->top st))
                       0)
                (equal (directional-override-kind
                        (directional-status->override
                         (explicit-state->top st)))
                       :neutral))
           (b* (((mv levels classes)
                 (bidi-explicit-levels-from (bidi-char-list-classes chars)
                                            st
                                            paragraph-level)))
             (equal (bidi-leveled-chars chars levels classes)
                    (flat-lchars chars))))
  :induct (list-induction chars)
  :enable (list-induction
           flat-lchars
           bidi-char-list-classes
           bidi-leveled-chars
           bidi-explicit-levels-from))

; Rule X9.

(defrulel bidi-remove-by-x9-when-lchars-flat-p
  (implies (lchars-flat-p lchars)
           (equal (bidi-remove-by-x9 lchars)
                  (bidi-leveled-char-list-fix lchars)))
  :induct (list-induction lchars)
  :enable (list-induction
           bidi-remove-by-x9
           lchar-flat-p
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

(defrulel bidi-leveled-char->level-of-bidi-leveled-char-at-when-flat
  (implies (lchars-flat-p lchars)
           (equal (bidi-leveled-char->level
                   (bidi-leveled-char-at position lchars))
                  0))
  :induct (bidi-leveled-char-at position lchars)
  :enable (bidi-leveled-char-at
           lchar-flat-p))

(defrulel bidi-leveled-char->original-of-bidi-leveled-char-at-when-flat
  (implies (lchars-flat-p lchars)
           (bidi-plain-class-p
            (bidi-leveled-char->original
             (bidi-leveled-char-at position lchars))))
  :induct (bidi-leveled-char-at position lchars)
  :enable (bidi-leveled-char-at
           lchar-flat-p
           bidi-plain-class-p))

(defrulel not-isolate-when-bidi-plain-class-p
  (implies (bidi-plain-class-p class)
           (and (not (bidi-class-isolate-initiator-p class))
                (not (equal (bidi-class-kind class)
                            :pop-directional-isolate))))
  :enable (bidi-plain-class-p
           bidi-class-isolate-formatting-p))

(defrulel bidi-sequence-successor-when-flat
  (implies (lchars-flat-p lchars)
           (equal (bidi-sequence-successor position lchars)
                  (and (< (+ 1 (nfix position)) (len lchars))
                       (+ 1 (nfix position)))))
  :enable (bidi-sequence-successor
           nfix
           natp))

(defrulel bidi-sequence-from-when-flat
  (implies (lchars-flat-p lchars)
           (equal (bidi-sequence-from position lchars)
                  (nat-range position (len lchars))))
  :induct (bidi-sequence-from position lchars)
  :enable (bidi-sequence-from
           nat-range
           nfix
           natp))

(defrulel bidi-sequence-start-p-when-flat
  (implies (lchars-flat-p lchars)
           (equal (bidi-sequence-start-p position lchars)
                  (and (< (nfix position) (len lchars))
                       (equal (nfix position) 0))))
  :enable (bidi-sequence-start-p
           nfix
           natp))

(defrulel bidi-level-at-when-flat
  (implies (lchars-flat-p lchars)
           (equal (bidi-level-at position lchars 0)
                  0))
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
; one call of BIDI-RESOLVE-SEQUENCE, with sos = eos = L.

(defrulel bidi-resolve-sequence-at-when-flat
  (implies (and (lchars-flat-p lchars)
                (consp positions))
           (equal (bidi-resolve-sequence-at positions lchars 0)
                  (b* ((sequence (bidi-leveled-chars-at positions lchars)))
                    (bidi-resolve-sequence
                     (bidi-leveled-char-list-classes sequence)
                     (bidi-leveled-char-list-brackets sequence)
                     (bidi-class-left-to-right)
                     (bidi-class-left-to-right)
                     0))))
  :enable (bidi-resolve-sequence-at
           bidi-level-direction))

(defrulel bidi-resolve-sequences-from-when-flat-and-not-first
  (implies (and (lchars-flat-p lchars)
                (natp position)
                (< 0 position))
           (equal (bidi-resolve-sequences-from position lchars 0 levels)
                  (nat-list-fix levels)))
  :induct (bidi-resolve-sequences-from position lchars 0 levels)
  :enable (bidi-resolve-sequences-from
           nfix
           natp))

(defrulel consp-of-nat-range-of-0
  (implies (consp x)
           (consp (nat-range 0 (len x))))
  :expand ((len x)
           (nat-range 0 (+ 1 (len (cdr x))))))

(defrulel bidi-resolve-sequences-from-when-flat
  (implies (and (lchars-flat-p lchars)
                (bidi-leveled-char-listp lchars)
                (equal (len levels) (len lchars)))
           (equal (bidi-resolve-sequences-from 0 lchars 0 levels)
                  (if (consp lchars)
                      (bidi-resolve-sequence
                       (bidi-leveled-char-list-classes lchars)
                       (bidi-leveled-char-list-brackets lchars)
                       (bidi-class-left-to-right)
                       (bidi-class-left-to-right)
                       0)
                    (nat-list-fix levels))))
  :expand (bidi-resolve-sequences-from 0 lchars 0 levels)
  :enable len)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Rule L1 and the levels of all the characters:
; a level stays, or becomes the paragraph embedding level, which is 0.

(defrulel bidi-outside-zero-p-of-bidi-reset-levels
  (implies (bidi-outside-zero-p outside levels)
           (bidi-outside-zero-p outside
                                (mv-nth 0 (bidi-reset-levels lchars levels 0))))
  :induct (three-lists-induction outside levels lchars)
  :enable (three-lists-induction
           bidi-outside-zero-p
           bidi-reset-levels))

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

(defrulel bidi-outside-zero-p-of-bidi-reset-all-levels
  (implies (bidi-outside-zero-p outside levels)
           (bidi-outside-zero-p
            outside
            (mv-nth 0 (bidi-reset-all-levels classes levels 0))))
  :induct (three-lists-induction outside levels classes)
  :enable (three-lists-induction
           bidi-outside-zero-p
           bidi-reset-all-levels))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The theorem of this book.

(defrulel bidi-outside-zero-p-of-no-levels
  (bidi-outside-zero-p outside nil)
  :expand (bidi-outside-zero-p outside nil))

(defrulel bidi-reset-all-levels-of-nil
  (equal (mv-nth 0 (bidi-reset-all-levels nil levels level))
         nil)
  :expand (bidi-reset-all-levels nil levels level))

(defrulel flat-lchars-under-iff
  (iff (flat-lchars chars)
       (consp chars))
  :expand (flat-lchars chars))

(defrulel bidi-char-list-classes-when-not-consp
  (implies (not (consp chars))
           (equal (bidi-char-list-classes chars)
                  nil))
  :expand (bidi-char-list-classes chars))

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
  :enable (bidi-paragraph-all-levels
           bidi-paragraph-levels
           bidi-explicit-levels))
