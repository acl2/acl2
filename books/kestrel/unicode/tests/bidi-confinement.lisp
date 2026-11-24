; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of confinement.
;
; That a plain text whose segments are guarded is confined is a theorem
; of the library (book bidi-guarded-theorem.lisp).
; Here it is also checked, by running the algorithm, on every text
; of one to four characters over sixteen characters,
; with every way of cutting the text into segments;
; and examples show that each of the conditions is needed.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../bidi-confinement")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic-5/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The sixteen characters: one of each of the twelve bidirectional classes
; that a plain text can have (the last of them, ON, is the exclamation mark),
; and two kinds of paired brackets, which are also of class ON.
;
;   a          L      Latin letter
;   U+05D0     R      Hebrew letter alef
;   U+0627     AL     Arabic letter alef
;   1          EN     European digit
;   U+0661     AN     Arabic-Indic digit one
;   +          ES     plus sign
;   %          ET     percent sign
;   ,          CS     comma
;   U+0301     NSM    combining acute accent
;   space      WS
;   tab        S
;   !          ON
;   ( ) [ ]    ON     paired brackets

(defconst *bidi-confinement-test-characters*
  '(#x61 #x5D0 #x627 #x31 #x661 #x2B #x25 #x2C #x301 #x20 #x9 #x21
    #x28 #x29 #x5B #x5D))

(assert-event
 (bidi-plain-p *bidi-confinement-test-characters* (version-v16.0.0)))
(assert-event
 (bidi-plain-p *bidi-confinement-test-characters* (version-v17.0.0)))
(assert-event
 (bidi-plain-p *bidi-confinement-test-characters* (version-v18.0.0)))

;;;;;;;;;;;;;;;;;;;;

; The text of a given length with a given number:
; the digits of the number in base 16 say which characters it has.

(define bidi-confinement-test-text ((index natp) (length natp))
  :returns (cps code-point-listp)
  (b* (((when (zp length)) nil)
       (index (lnfix index)))
    (cons (code-point-fix (nth (mod index 16)
                               *bidi-confinement-test-characters*))
          (bidi-confinement-test-text (floor index 16) (- length 1))))
  :hooks nil)

; The segments of a text for a number: the text is cut
; after its first character if the number is odd,
; after its second character if half the number is odd, and so on.

(define bidi-confinement-test-segments ((cps code-point-listp) (mask natp))
  :returns (segments code-point-list-listp
                     :hints (("Goal" :induct t)))
  (b* (((when (endp cps)) nil)
       (cp (code-point-fix (car cps)))
       ((when (endp (cdr cps))) (list (list cp)))
       (mask (lnfix mask))
       (rest (bidi-confinement-test-segments (cdr cps) (floor mask 2)))
       ((when (oddp mask)) (cons (list cp) rest)))
    (cons (cons cp (code-point-list-fix (car rest)))
          (code-point-list-list-fix (cdr rest))))
  :verify-guards :after-returns
  :hooks nil)

; Count the ways of cutting a text whose segments are guarded:
; those for which the text is confined, and the others.

(define bidi-confinement-test-masks ((cps code-point-listp)
                                     (mask natp)
                                     (count natp)
                                     (ver versionp)
                                     (confined natp)
                                     (others natp))
  :returns (mv (new-confined natp :rule-classes :type-prescription)
               (new-others natp :rule-classes :type-prescription))
  (b* ((mask (lnfix mask))
       (count (lnfix count))
       (confined (lnfix confined))
       (others (lnfix others))
       ((when (>= mask count)) (mv confined others))
       (segments (bidi-confinement-test-segments cps mask))
       ((unless (bidi-guarded-segments-p segments ver))
        (bidi-confinement-test-masks cps (+ 1 mask) count ver
                                     confined others))
       ((when (bidi-confined-p segments ver))
        (bidi-confinement-test-masks cps (+ 1 mask) count ver
                                     (+ 1 confined) others)))
    (bidi-confinement-test-masks cps (+ 1 mask) count ver
                                 confined (+ 1 others)))
  :measure (nfix (- (nfix count) (nfix mask)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks nil)

(define bidi-confinement-test-texts ((index natp)
                                     (count natp)
                                     (length posp)
                                     (ver versionp)
                                     (confined natp)
                                     (others natp))
  :returns (mv (new-confined natp :rule-classes :type-prescription)
               (new-others natp :rule-classes :type-prescription))
  (b* ((index (lnfix index))
       (count (lnfix count))
       (confined (lnfix confined))
       (others (lnfix others))
       ((when (>= index count)) (mv confined others))
       (cps (bidi-confinement-test-text index length))
       ((mv confined others)
        (bidi-confinement-test-masks cps
                                     0
                                     (expt 2 (- (acl2::lposfix length) 1))
                                     ver
                                     confined
                                     others)))
    (bidi-confinement-test-texts (+ 1 index) count length ver
                                 confined others))
  :measure (nfix (- (nfix count) (nfix index)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks nil)

; All the texts of a length, with all the ways of cutting them.

(define bidi-confinement-test ((length posp) (ver versionp))
  :returns (mv (confined natp :rule-classes :type-prescription)
               (others natp :rule-classes :type-prescription))
  (bidi-confinement-test-texts 0
                               (expt 16 (acl2::lposfix length))
                               length
                               ver
                               0
                               0)
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;

; In each test, the first number is how many of the cases have
; guarded segments, and the second is how many of those are not confined.

(defmacro bidi-confinement-test-is (length ver confined)
  `(assert-event
    (mv-let (confined others)
        (bidi-confinement-test ,length ,ver)
      (and (equal confined ,confined)
           (equal others 0)))))

(bidi-confinement-test-is 1 (version-v16.0.0) 16)
(bidi-confinement-test-is 1 (version-v17.0.0) 16)
(bidi-confinement-test-is 1 (version-v18.0.0) 16)

(bidi-confinement-test-is 2 (version-v16.0.0) 494)
(bidi-confinement-test-is 2 (version-v17.0.0) 494)
(bidi-confinement-test-is 2 (version-v18.0.0) 494)

(bidi-confinement-test-is 3 (version-v16.0.0) 14824)
(bidi-confinement-test-is 3 (version-v17.0.0) 14824)
(bidi-confinement-test-is 3 (version-v18.0.0) 14824)

(bidi-confinement-test-is 4 (version-v17.0.0) 435434)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples.  Alef, bet, gimel and dalet are the Hebrew letters
; U+05D0, U+05D1, U+05D2 and U+05D3, of class R.

(defmacro test (form)
  `(assert-event ,form))

(defconst *v17* (version-v17.0.0))

(defconst *ltr* (paragraph-direction-left-to-right))

; The segments (, def, space, alef bet, space, x, ) are guarded,
; and the text is confined: bet and alef change places,
; and everything else stays where it is.

(defconst *confined-example*
  '((#x28) (#x64 #x65 #x66) (#x20) (#x5D0 #x5D1) (#x20) (#x78) (#x29)))

(test (bidi-plain-p (acl2::flatten *confined-example*) *v17*))
(test (bidi-guarded-segments-p *confined-example* *v17*))
(test (bidi-confined-p *confined-example* *v17*))
(test (equal (bidi-display (acl2::flatten *confined-example*) *ltr* *v17*)
             '(#x28 #x64 #x65 #x66 #x20 #x5D1 #x5D0 #x20 #x78 #x29)))

; A digit at the end of a right-to-left segment is displayed at its left,
; inside the segment: x, space, =, space, alef bet 1, semicolon.

(defconst *confined-example-with-digit*
  '((#x78) (#x20) (#x3D) (#x20) (#x5D0 #x5D1 #x31) (#x3B)))

(test (bidi-guarded-segments-p *confined-example-with-digit* *v17*))
(test (bidi-confined-p *confined-example-with-digit* *v17*))
(test (equal (bidi-display (acl2::flatten *confined-example-with-digit*)
                           *ltr* *v17*)
             '(#x78 #x20 #x3D #x20 #x31 #x5D1 #x5D0 #x3B)))

; Condition 1.  Alef bet, space, gimel dalet: after the first segment
; the first letter is not a left-to-right letter.
; The text is not confined, and the two words are displayed
; in the opposite order.

(defconst *two-words* '((#x5D0 #x5D1) (#x20) (#x5D2 #x5D3)))

(test (not (bidi-guarded-segments-p *two-words* *v17*)))
(test (not (bidi-confined-p *two-words* *v17*)))
(test (equal (bidi-display (acl2::flatten *two-words*) *ltr* *v17*)
             '(#x5D3 #x5D2 #x20 #x5D1 #x5D0)))

; With U+200E LEFT-TO-RIGHT MARK, of class L, after the first word,
; the segments are guarded, the text is confined,
; and the two words are displayed in the order in which they are stored.

(defconst *two-words-with-mark*
  '((#x5D0 #x5D1) (#x200E) (#x20) (#x5D2 #x5D3)))

(test (bidi-plain-p (acl2::flatten *two-words-with-mark*) *v17*))
(test (bidi-guarded-segments-p *two-words-with-mark* *v17*))
(test (bidi-confined-p *two-words-with-mark* *v17*))
(test (equal (bidi-display (acl2::flatten *two-words-with-mark*) *ltr* *v17*)
             '(#x5D1 #x5D0 #x200E #x20 #x5D3 #x5D2)))

; Condition 1 again: alef, space, 1.  The digit is displayed first.

(test (not (bidi-guarded-segments-p '((#x5D0) (#x20) (#x31)) *v17*)))
(test (not (bidi-confined-p '((#x5D0) (#x20) (#x31)) *v17*)))
(test (equal (bidi-display '(#x5D0 #x20 #x31) *ltr* *v17*)
             '(#x31 #x20 #x5D0)))

; Condition 2, class ET.  Alef 1, then a percent sign:
; the percent sign is displayed between the digit and the letter.

(test (not (bidi-guarded-segments-p '((#x5D0 #x31) (#x25)) *v17*)))
(test (not (bidi-confined-p '((#x5D0 #x31) (#x25)) *v17*)))
(test (equal (bidi-display '(#x5D0 #x31 #x25) *ltr* *v17*)
             '(#x31 #x25 #x5D0)))

; Condition 2, class NSM.  Alef, then U+0301 COMBINING ACUTE ACCENT:
; the mark gets the level of the letter.

(test (not (bidi-guarded-segments-p '((#x5D0) (#x301)) *v17*)))
(test (not (bidi-confined-p '((#x5D0) (#x301)) *v17*)))

; Condition 3.  Alef, space, (, bet, then ): the bracket pair opens
; inside the first segment and closes after it.
; The closing parenthesis is displayed at the left end,
; as its mirror image.

(test (not (bidi-guarded-segments-p '((#x5D0 #x20 #x28 #x5D1) (#x29))
                                    *v17*)))
(test (not (bidi-confined-p '((#x5D0 #x20 #x28 #x5D1) (#x29)) *v17*)))
(test (equal (bidi-display '(#x5D0 #x20 #x28 #x5D1 #x29) *ltr* *v17*)
             '(#x28 #x5D1 #x29 #x20 #x5D0)))

; A confined text is displayed segment by segment,
; but a segment need not be displayed as it would be alone.
; Here the segments are ( and bet, space, [, alef, space, ), space, ].
; They are guarded and the text is confined.
; In the text, the parentheses are a bracket pair
; and the square brackets are not; alone, in the second segment,
; it is the other way around.

(defconst *brackets-across*
  '((#x28) (#x5D1 #x20 #x5B #x5D0 #x20 #x29 #x20 #x5D)))

(test (bidi-guarded-segments-p *brackets-across* *v17*))
(test (bidi-confined-p *brackets-across* *v17*))
(test (equal (bidi-display (acl2::flatten *brackets-across*) *ltr* *v17*)
             '(#x28 #x5D0 #x5D #x20 #x5D1 #x20 #x29 #x20 #x5D)))
(test (equal (bidi-display (cadr *brackets-across*) *ltr* *v17*)
             '(#x5B #x20 #x28 #x20 #x5D0 #x5D #x20 #x5D1)))

; Texts that are not plain: a character of class BN (U+200D),
; an explicit formatting character (U+202E),
; and a paragraph separator (U+000A).

(test (not (bidi-plain-p '(#x61 #x200D) *v17*)))
(test (not (bidi-plain-p '(#x61 #x202E) *v17*)))
(test (not (bidi-plain-p '(#x61 #xA) *v17*)))
