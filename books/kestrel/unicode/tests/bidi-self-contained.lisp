; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of self-contained segments.
;
; That, in a plain text whose segments are self-contained,
; each segment is displayed as it is alone is a theorem of the library
; (book bidi-self-contained.lisp).
; Here it is also checked, by running the algorithm, on every text
; of one to four characters over sixteen characters,
; with every way of cutting the text into segments;
; and examples show that each of the two conditions
; that are added to those on guarded segments is needed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../bidi-self-contained")

; The texts and the ways of cutting them are those of the tests
; of confinement: the sixteen characters are one of each
; of the twelve bidirectional classes that a plain text can have,
; and two kinds of paired brackets.
(include-book "bidi-confinement")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic-5/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that some segments have the property that the two theorems state,
; given the levels of the characters of the text
; when the paragraph goes from left to right, and the display of the text:
; the levels are those that the characters have when each segment is alone,
; and the display is the display of each segment, one after the other.

(define bidi-self-contained-test-segments ((segments code-point-list-listp)
                                           (cps code-point-listp)
                                           levels
                                           display
                                           (ver versionp))
  :returns (yes/no booleanp)
  (and (equal (acl2::flatten segments)
              cps)
       (equal (bidi-levels-of-each-segment segments ver)
              levels)
       (equal (bidi-display-of-each-segment
               segments
               (paragraph-direction-left-to-right)
               ver)
              display))
  :hooks nil)

; Count the ways of cutting a text whose segments are self-contained:
; those that have the property, and the others.

(define bidi-self-contained-test-masks ((cps code-point-listp)
                                        (mask natp)
                                        (count natp)
                                        levels
                                        display
                                        (ver versionp)
                                        (good natp)
                                        (bad natp))
  :returns (mv (new-good natp :rule-classes :type-prescription)
               (new-bad natp :rule-classes :type-prescription))
  (b* ((mask (lnfix mask))
       (count (lnfix count))
       (good (lnfix good))
       (bad (lnfix bad))
       ((when (>= mask count)) (mv good bad))
       (segments (bidi-confinement-test-segments cps mask))
       ((unless (bidi-self-contained-segments-p segments ver))
        (bidi-self-contained-test-masks cps (+ 1 mask) count
                                        levels display ver
                                        good bad))
       ((when (bidi-self-contained-test-segments segments cps
                                                 levels display ver))
        (bidi-self-contained-test-masks cps (+ 1 mask) count
                                        levels display ver
                                        (+ 1 good) bad)))
    (bidi-self-contained-test-masks cps (+ 1 mask) count
                                    levels display ver
                                    good (+ 1 bad)))
  :measure (nfix (- (nfix count) (nfix mask)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks nil)

; The levels and the display of a text do not depend on how it is cut:
; they are calculated once for each text.

(define bidi-self-contained-test-texts ((index natp)
                                        (count natp)
                                        (length posp)
                                        (ver versionp)
                                        (good natp)
                                        (bad natp))
  :returns (mv (new-good natp :rule-classes :type-prescription)
               (new-bad natp :rule-classes :type-prescription))
  (b* ((index (lnfix index))
       (count (lnfix count))
       (good (lnfix good))
       (bad (lnfix bad))
       ((when (>= index count)) (mv good bad))
       (cps (bidi-confinement-test-text index length))
       (levels (bidi-paragraph-all-levels
                (code-points-to-bidi-chars cps ver)
                0))
       (display (bidi-display cps (paragraph-direction-left-to-right) ver))
       ((mv good bad)
        (bidi-self-contained-test-masks cps
                                        0
                                        (expt 2 (- (acl2::lposfix length) 1))
                                        levels
                                        display
                                        ver
                                        good
                                        bad)))
    (bidi-self-contained-test-texts (+ 1 index) count length ver good bad))
  :measure (nfix (- (nfix count) (nfix index)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks nil)

; All the texts of a length, with all the ways of cutting them.

(define bidi-self-contained-test ((length posp) (ver versionp))
  :returns (mv (good natp :rule-classes :type-prescription)
               (bad natp :rule-classes :type-prescription))
  (bidi-self-contained-test-texts 0
                                  (expt 16 (acl2::lposfix length))
                                  length
                                  ver
                                  0
                                  0)
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

; In each test, the number is how many of the cases have
; self-contained segments.  In none of them
; do the levels or the display differ from those of the segments alone.
; The cases with guarded segments are 16, 494, 14824 and 435434
; (see the tests of confinement): all those of lengths 1 and 2
; are self-contained, and all but 12 and 1182 of those of lengths 3 and 4.

(defmacro bidi-self-contained-test-is (length ver good)
  `(assert-event
    (mv-let (good bad)
        (bidi-self-contained-test ,length ,ver)
      (and (equal good ,good)
           (equal bad 0)))))

(bidi-self-contained-test-is 1 (version-v16.0.0) 16)
(bidi-self-contained-test-is 1 (version-v17.0.0) 16)
(bidi-self-contained-test-is 1 (version-v18.0.0) 16)

(bidi-self-contained-test-is 2 (version-v16.0.0) 494)
(bidi-self-contained-test-is 2 (version-v17.0.0) 494)
(bidi-self-contained-test-is 2 (version-v18.0.0) 494)

(bidi-self-contained-test-is 3 (version-v16.0.0) 14812)
(bidi-self-contained-test-is 3 (version-v17.0.0) 14812)
(bidi-self-contained-test-is 3 (version-v18.0.0) 14812)

(bidi-self-contained-test-is 4 (version-v17.0.0) 434252)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples.  Alef, bet and gimel are the Hebrew letters
; U+05D0, U+05D1 and U+05D2, of class R.
; The macro TEST and the constants *V17* and *LTR*
; are those of the tests of confinement.

; The levels of the characters of a text
; when the paragraph goes from left to right.

(define bidi-self-contained-test-levels ((cps code-point-listp)
                                         (ver versionp))
  :returns (levels nat-listp)
  (bidi-paragraph-all-levels (code-points-to-bidi-chars cps ver) 0)
  :hooks nil)

; The segments x, space, =, space; then alef, [, bet, ], 1; then
; semicolon, space, y are self-contained.
; The second segment is displayed from right to left,
; with the digit at its left and the brackets as their mirror images,
; in the text as it is alone.

(defconst *self-contained-example*
  '((#x78 #x20 #x3D #x20) (#x5D0 #x5B #x5D1 #x5D #x31) (#x3B #x20 #x79)))

(test (bidi-plain-p (acl2::flatten *self-contained-example*) *v17*))
(test (bidi-self-contained-segments-p *self-contained-example* *v17*))
(test (equal (bidi-display (cadr *self-contained-example*) *ltr* *v17*)
             '(#x31 #x5B #x5D1 #x5D #x5D0)))
(test (equal (bidi-display (acl2::flatten *self-contained-example*)
                           *ltr* *v17*)
             '(#x78 #x20 #x3D #x20 #x31 #x5B #x5D1 #x5D #x5D0 #x3B #x20 #x79)))
(test (equal (bidi-display (acl2::flatten *self-contained-example*)
                           *ltr* *v17*)
             (bidi-display-of-each-segment *self-contained-example*
                                           *ltr* *v17*)))
(test (equal (bidi-self-contained-test-levels
              (acl2::flatten *self-contained-example*) *v17*)
             '(0 0 0 0 1 1 1 1 2 0 0 0)))
(test (equal (bidi-self-contained-test-levels
              (acl2::flatten *self-contained-example*) *v17*)
             (bidi-levels-of-each-segment *self-contained-example* *v17*)))

; The condition on the closing brackets.
; The text is a, space, (, bet, ), space, gimel,
; and it is cut after the opening parenthesis.
; The segments are guarded and the text is confined,
; but the bracket pair closes inside the second segment,
; which is a right-to-left segment, and opens before it.
; In the text the two parentheses get the direction of the paragraph,
; and the characters of the second segment are displayed
; in the order in which they are stored.
; Alone, the second segment is displayed from right to left as a whole.

(defconst *closes-inside* '((#x61 #x20 #x28) (#x5D1 #x29 #x20 #x5D2)))

(test (bidi-plain-p (acl2::flatten *closes-inside*) *v17*))
(test (bidi-guarded-segments-p *closes-inside* *v17*))
(test (bidi-confined-p *closes-inside* *v17*))
(test (not (bidi-self-contained-segments-p *closes-inside* *v17*)))
(test (equal (bidi-display (acl2::flatten *closes-inside*) *ltr* *v17*)
             '(#x61 #x20 #x28 #x5D1 #x29 #x20 #x5D2)))
(test (equal (bidi-display (cadr *closes-inside*) *ltr* *v17*)
             '(#x5D2 #x20 #x28 #x5D1)))
(test (equal (bidi-self-contained-test-levels
              (acl2::flatten *closes-inside*) *v17*)
             '(0 0 0 1 0 0 1)))
(test (equal (bidi-levels-of-each-segment *closes-inside* *v17*)
             '(0 0 0 1 1 1 1)))

; The same text cut before the opening parenthesis:
; the bracket pair opens and closes in the second segment,
; and the segments are self-contained.

(defconst *opens-inside* '((#x61 #x20) (#x28 #x5D1 #x29 #x20 #x5D2)))

(test (bidi-self-contained-segments-p *opens-inside* *v17*))
(test (equal (bidi-display (cadr *opens-inside*) *ltr* *v17*)
             '(#x28 #x5D1 #x29 #x20 #x5D2)))
(test (equal (bidi-display (acl2::flatten *opens-inside*) *ltr* *v17*)
             (bidi-display-of-each-segment *opens-inside* *ltr* *v17*)))
(test (equal (bidi-self-contained-test-levels
              (acl2::flatten *opens-inside*) *v17*)
             (bidi-levels-of-each-segment *opens-inside* *v17*)))

; The example of the tests of confinement in which a segment
; is not displayed as it would be alone: its segments are guarded,
; but they are not self-contained.

(test (bidi-guarded-segments-p *brackets-across* *v17*))
(test (not (bidi-self-contained-segments-p *brackets-across* *v17*)))

; The condition that the search for the bracket pairs does not give up.
; The first segment is 63 opening parentheses, and the second is
; bet, (, gimel, ), a.  The segments are guarded, and no bracket pair
; of the text closes in the second segment after opening before it.
; But the opening parenthesis of the second segment is the 64th
; that waits for its closing parenthesis: the search gives up,
; and the text has no bracket pair at all.
; In the text the closing parenthesis, between gimel and a,
; gets the direction of the paragraph and stays where it is.
; Alone, the second segment has a bracket pair
; that is displayed from right to left with the two letters.

(defconst *too-deep*
  (list (repeat 63 #x28) '(#x5D1 #x28 #x5D2 #x29 #x61)))

(test (bidi-plain-p (acl2::flatten *too-deep*) *v17*))
(test (bidi-guarded-segments-p *too-deep* *v17*))
(test (not (bidi-self-contained-segments-p *too-deep* *v17*)))
(test (b* ((chars (code-points-to-bidi-chars (acl2::flatten *too-deep*)
                                             *v17*))
           (classes (bidi-char-list-classes chars))
           (roles (bidi-char-list-brackets chars)))
        (and (bidi-bracket-pairs-overflow-p classes roles)
             (not (bidi-bracket-pairs classes roles)))))
(test (equal (nthcdr 63 (bidi-display (acl2::flatten *too-deep*) *ltr* *v17*))
             '(#x5D2 #x29 #x5D1 #x29 #x61)))
(test (equal (bidi-display (cadr *too-deep*) *ltr* *v17*)
             '(#x28 #x5D2 #x29 #x5D1 #x61)))
(test (equal (nthcdr 63 (bidi-self-contained-test-levels
                         (acl2::flatten *too-deep*) *v17*))
             '(1 1 1 0 0)))
(test (equal (nthcdr 63 (bidi-levels-of-each-segment *too-deep* *v17*))
             '(1 1 1 1 0)))

; With one opening parenthesis less in the first segment,
; the search does not give up and the segments are self-contained.

(defconst *not-too-deep*
  (list (repeat 62 #x28) '(#x5D1 #x28 #x5D2 #x29 #x61)))

(test (bidi-self-contained-segments-p *not-too-deep* *v17*))
(test (equal (bidi-display (acl2::flatten *not-too-deep*) *ltr* *v17*)
             (bidi-display-of-each-segment *not-too-deep* *ltr* *v17*)))
(test (equal (bidi-self-contained-test-levels
              (acl2::flatten *not-too-deep*) *v17*)
             (bidi-levels-of-each-segment *not-too-deep* *v17*)))
