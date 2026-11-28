; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-rule-display-order")
(include-book "bidi-rule-display-levels")
(include-book "bidi-rule-left-to-right-label")

(local (include-book "bidi-left-to-right"))
(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; A name that the wide rule allows is one paragraph.

(defrulel bidi-paragraph-length-when-wide
  (implies (bidi-rule-wide-code-points-p name ver)
           (equal (bidi-paragraph-length (code-points-to-bidi-chars name ver))
                  (len name)))
  :induct (len name)
  :expand ((code-points-to-bidi-chars name ver)
           (:free (a b) (bidi-paragraph-length (cons a b)))
           (bidi-paragraph-length nil))
  :enable (len
           code-point-bidi-char
           bidi-rule-wide-code-point-p))

; A name without a letter of class R or AL and without a digit of class AN
; is described as displayed in the order in which it is stored.

(defrulel bidi-name-start-when-no-letter
  (implies (and (not (bidi-class-kind-present-p :right-to-left name ver))
                (not (bidi-class-kind-present-p :arabic-letter name ver)))
           (equal (bidi-name-start name ver)
                  (len name)))
  :induct (len name)
  :enable (len
           bidi-name-start
           bidi-right-to-left-letter-p)
  :expand ((bidi-class-kind-present-p :right-to-left name ver)
           (bidi-class-kind-present-p :arabic-letter name ver)))

(defrulel bidi-name-display-when-not-right-to-left-label
  (implies (not (bidi-right-to-left-label-p name ver))
           (equal (bidi-name-display name ver)
                  (code-point-list-fix name)))
  :enable (bidi-name-display
           bidi-right-to-left-label-p)
  :use (:instance bidi-name-end-upper-bound
                  (name (code-point-list-fix name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-display-theorem
  :parents (bidi-rule-display)
  :short "Theorems that the Unicode Bidirectional Algorithm,
          in a paragraph from left to right,
          displays a name that the wide rule allows
          as @(tsee bidi-name-display) says,
          and that no two such names are displayed alike."

  (defrule bidi-display-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name ver)
                  (equal (paragraph-direction-kind direction) :left-to-right))
             (equal (bidi-display name direction ver)
                    (bidi-name-display name ver)))
    :cases ((bidi-right-to-left-label-p name ver))
    :enable (bidi-display
             bidi-arrange-paragraph
             bidi-paragraph-embedding-level
             bidi-paragraph-all-levels-when-bidi-rule-wide-p
             right-to-left-free-p-when-bidi-rule-wide-p
             bidi-rule-wide-p))

  (defrule bidi-display-is-one-to-one-when-bidi-rule-wide-p
    (implies (and (bidi-rule-wide-p name1 ver)
                  (bidi-rule-wide-p name2 ver)
                  (equal (paragraph-direction-kind direction) :left-to-right)
                  (equal (bidi-display name1 direction ver)
                         (bidi-display name2 direction ver)))
             (equal (code-point-list-fix name1)
                    (code-point-list-fix name2)))
    :rule-classes nil
    :use bidi-name-display-is-one-to-one))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The strict rule, in a paragraph of any direction.

; A name that the strict rule allows is one that the wide rule allows.

(defrulel bidi-rule-wide-code-points-p-when-bidi-rule-strict-p
  (implies (bidi-rule-strict-p name ver)
           (bidi-rule-wide-code-points-p name ver))
  :enable bidi-rule-wide-p
  :disable bidi-rule-wide-p-when-bidi-rule-strict-p
  :use (:instance bidi-rule-wide-p-when-bidi-rule-strict-p (label name)))

; What the strict rule says of a right-to-left label:
; its first character is a letter of class R or AL,
; the last character that is not a mark is a letter or a digit,
; and no character is of class L.

(defrulel right-to-left-label-when-bidi-rule-strict-p
  (implies (and (bidi-rule-strict-p name ver)
                (bidi-right-to-left-label-p name ver))
           (and (consp name)
                (bidi-right-to-left-letter-p (car name) ver)
                (bidi-rule-right-to-left-end-p name ver)
                (not (bidi-class-kind-present-p :left-to-right name ver))))
  :rule-classes :forward-chaining
  :enable (bidi-rule-strict-p
           bidi-rule-p
           bidi-rule-wide-p
           bidi-right-to-left-letter-p)
  :disable bidi-rule-wide-p-when-bidi-rule-strict-p
  :use (:instance bidi-rule-wide-p-when-bidi-rule-strict-p (label name)))

(defrulel not-bidi-mark-code-point-p-when-bidi-right-to-left-letter-p
  (implies (bidi-right-to-left-letter-p cp ver)
           (not (bidi-mark-code-point-p cp ver)))
  :enable (bidi-right-to-left-letter-p
           bidi-mark-code-point-p))

; The middle part of such a label is the whole label:
; it starts at the first character,

(defrulel bidi-name-start-when-first-is-letter
  (implies (and (consp name)
                (bidi-right-to-left-letter-p (car name) ver))
           (equal (bidi-name-start name ver)
                  0))
  :expand (bidi-name-start name ver))

; and it ends after the last character, because only marks
; come after the last letter or digit.

(defrulel bidi-name-to-last-letter-or-digit-when-bidi-marks-p
  (implies (bidi-marks-p x ver)
           (equal (bidi-name-to-last-letter-or-digit x ver)
                  0))
  :induct (len x)
  :enable (len
           bidi-name-to-last-letter-or-digit
           bidi-mark-code-point-p
           bidi-right-to-left-letter-p
           bidi-digit-p))

(defrulel bidi-name-to-last-letter-or-digit-when-right-to-left-end
  (implies (bidi-rule-right-to-left-end-p x ver)
           (< 0 (bidi-name-to-last-letter-or-digit x ver)))
  :rule-classes :linear
  :induct (len x)
  :enable (len
           bidi-name-to-last-letter-or-digit
           bidi-rule-right-to-left-end-p
           bidi-right-to-left-letter-p
           bidi-digit-p))

(defrulel bidi-leading-marks-when-bidi-marks-p
  (implies (bidi-marks-p x ver)
           (equal (bidi-leading-marks x ver)
                  (len x)))
  :induct (len x)
  :enable (len bidi-leading-marks))

(defrulel len-below-bidi-leading-marks-of-nthcdr-when-bidi-marks-p
  (implies (and (bidi-marks-p x ver)
                (natp k))
           (<= (len x)
               (+ k (bidi-leading-marks (nthcdr k x) ver))))
  :rule-classes :linear
  :enable (nfix fix))

(defrulel len-below-bidi-leading-marks-of-nthcdr-when-right-to-left-end
  (implies (and (bidi-rule-right-to-left-end-p x ver)
                (natp n)
                (<= (bidi-name-to-last-letter-or-digit x ver) n))
           (<= (len x)
               (+ n (bidi-leading-marks (nthcdr n x) ver))))
  :rule-classes :linear
  :induct (nthcdr n x)
  :enable (nthcdr
           len
           nfix
           fix
           bidi-name-to-last-letter-or-digit
           bidi-rule-right-to-left-end-p))

(defrulel bidi-name-end-when-right-to-left-end
  (implies (bidi-rule-right-to-left-end-p name ver)
           (equal (bidi-name-end name ver)
                  (len name)))
  :enable (bidi-name-end max)
  :disable bidi-name-end-upper-bound
  :use bidi-name-end-upper-bound)

; So the levels of the whole label are those of its middle part.

(defrulel bidi-name-levels-when-strict-right-to-left-label
  (implies (and (bidi-rule-strict-p name ver)
                (bidi-right-to-left-label-p name ver))
           (equal (bidi-name-levels name ver)
                  (bidi-middle-levels (bidi-clusters name ver) nil ver)))
  :enable bidi-name-levels
  :disable (right-to-left-label-when-bidi-rule-strict-p
            bidi-right-to-left-label-p-when-bidi-rule-p)
  :use (:instance right-to-left-label-when-bidi-rule-strict-p
                  (name (code-point-list-fix name))))

; A label whose characters are all at level 2 is displayed as it is stored.

(defrulel nat-listp-of-repeat-of-2
  (nat-listp (acl2::repeat n 2))
  :induct (acl2::repeat n 2)
  :enable acl2::repeat)

(defrulel bidi-mirror-chars-of-bidi-arrange-with-levels-of-repeat-of-2
  (equal (bidi-mirror-chars
          (bidi-arrange-with-levels cps (acl2::repeat (len cps) 2) ver)
          ver)
         (code-point-list-fix cps))
  :enable nfix)

; A left-to-right label, when the paragraph is not from right to left.

(defrulel bidi-display-when-left-to-right-label-and-not-right-to-left
  (implies (and (bidi-rule-strict-p name ver)
                (not (bidi-right-to-left-label-p name ver))
                (not (equal (paragraph-direction-kind direction)
                            :right-to-left)))
           (equal (bidi-display name direction ver)
                  (code-point-list-fix name)))
  :enable right-to-left-free-p-when-bidi-rule-wide-p)

; The paragraph embedding level that rules P2 and P3 find
; for a label whose first character is a letter of class R or AL.

(defrulel bidi-first-strong-level-when-first-is-letter
  (implies (and (consp name)
                (bidi-right-to-left-letter-p (car name) ver))
           (equal (bidi-first-strong-level
                   (bidi-char-list-classes (code-points-to-bidi-chars name ver))
                   nil)
                  1))
  :enable (bidi-first-strong-level
           bidi-right-to-left-letter-p
           bidi-class-strong-p
           bidi-class-right-to-left-p
           bidi-class-isolate-initiator-p
           code-point-bidi-char)
  :expand ((code-points-to-bidi-chars name ver)
           (:free (a b) (bidi-char-list-classes (cons a b)))
           (:free (a b) (bidi-first-strong (cons a b) 0 nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-rule-display-strict-theorem
  :parents (bidi-rule-display)
  :short "Theorems that the Unicode Bidirectional Algorithm,
          in a paragraph of any direction,
          displays a label that the strict rule allows
          as @(tsee bidi-name-display) says,
          and that no two such labels are displayed alike."
  :long
  (xdoc::topstring
   (xdoc::p
    "The strict rule is @(tsee bidi-rule-strict-p):
     the Bidi Rule of [RFC 5893]
     without the characters of class @('ET') (@('European_Terminator'))
     and @('BN') (@('Boundary_Neutral')).
     The label is the whole paragraph.")
   (xdoc::p
    "A right-to-left label that satisfies the strict rule
     begins with a letter of class @('R') (@('Right_To_Left'))
     or @('AL') (@('Arabic_Letter')),
     and only marks come after its last letter or digit.
     So the middle part of @(tsee bidi-name-levels) is the whole label,
     and no character has level 0.
     The first theorem says that the label gets those same levels
     in a paragraph from right to left,
     where the paragraph embedding level is 1.
     It follows from the theorem
     @('bidi-paragraph-all-levels-at-level-1-when-bidi-rule-wide-p')
     (see @(see bidi-rule-display-levels)).")
   (xdoc::p
    "The second theorem is for the three ways
     of giving the direction of the paragraph
     (see @(tsee paragraph-direction)).
     In a paragraph from left to right it is the theorem
     @('bidi-display-when-bidi-rule-wide-p')
     (see @(see bidi-rule-display-theorem)),
     since a label that the strict rule allows
     is one that the wide rule allows.
     In a paragraph from right to left,
     a right-to-left label has the same levels, by the first theorem,
     and so the same display;
     a left-to-right label has level 2 for each character
     (see @(see bidi-rule-left-to-right-label))
     and is displayed as it is stored,
     which is what @(tsee bidi-name-display) gives for it.
     When the direction is taken from the first strong character,
     the paragraph is from right to left for a right-to-left label,
     whose first character is a letter of class @('R') or @('AL'),
     and from left to right for a left-to-right label.")
   (xdoc::p
    "The third theorem follows from the second and from the theorem
     @('bidi-name-display-is-one-to-one')
     (see @(see bidi-rule-display-theorems)).
     The two labels can be in paragraphs of different directions:
     two labels that the strict rule allows are displayed alike
     only if they are the same label."))

  (defruled bidi-paragraph-all-levels-at-level-1-when-bidi-rule-strict-p
    (implies (and (bidi-rule-strict-p name ver)
                  (bidi-right-to-left-label-p name ver))
             (equal (bidi-paragraph-all-levels
                     (code-points-to-bidi-chars name ver)
                     1)
                    (bidi-name-levels name ver)))
    :enable bidi-paragraph-all-levels-at-level-1-when-bidi-rule-wide-p
    :disable bidi-right-to-left-label-p-when-bidi-rule-p)

  (defrule bidi-display-when-bidi-rule-strict-p
    (implies (bidi-rule-strict-p name ver)
             (equal (bidi-display name direction ver)
                    (bidi-name-display name ver)))
    :cases ((equal (paragraph-direction-kind direction) :left-to-right)
            (and (not (equal (paragraph-direction-kind direction)
                             :left-to-right))
                 (bidi-right-to-left-label-p name ver))
            (and (equal (paragraph-direction-kind direction) :right-to-left)
                 (not (bidi-right-to-left-label-p name ver))))
    :enable (bidi-display
             bidi-arrange-paragraph
             bidi-paragraph-embedding-level
             bidi-paragraph-all-levels-at-level-1-when-bidi-rule-strict-p
             bidi-paragraph-all-levels-at-level-1-when-left-to-right-label)
    :disable (bidi-right-to-left-label-p-when-bidi-rule-p
              bidi-name-levels-when-strict-right-to-left-label))

  (defrule bidi-display-is-one-to-one-when-bidi-rule-strict-p
    (implies (and (bidi-rule-strict-p name1 ver)
                  (bidi-rule-strict-p name2 ver)
                  (equal (bidi-display name1 direction1 ver)
                         (bidi-display name2 direction2 ver)))
             (equal (code-point-list-fix name1)
                    (code-point-list-fix name2)))
    :rule-classes nil
    :use bidi-name-display-is-one-to-one))
