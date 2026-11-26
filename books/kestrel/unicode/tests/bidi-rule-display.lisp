; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the display of a name computed without the rules
; of the algorithm, and of the way back (book bidi-rule-display.lisp).
;
; The first part has examples.
;
; The second part compares that display
; with the display of the Unicode Bidirectional Algorithm.
; That the two are the same for every name that satisfies the wide rule,
; in a paragraph from left to right, is a theorem
; (book bidi-rule-display-theorem.lisp); the search was written
; before the proof, and is kept as a test of the functions.
; A search goes through every list, up to a length,
; of the characters of a small set; for each list that satisfies the rule
; it checks that the two displays are the same
; and that the way back gives the list.
; The functions that make the lists are those of the tests
; of the Bidi Rule (file bidi-rule.lisp of this directory).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../bidi-rule-display")
(include-book "../bidirectional-algorithm")
(include-book "bidi-rule")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic-5/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples.
;
; The characters, with their classes:
;   a                       U+0061                    L
;   alef, bet               U+05D0, U+05D1 (Hebrew)   R
;   Arabic alef             U+0627                    AL
;   1, 2                    U+0031, U+0032            EN
;   Arabic-Indic one        U+0661                    AN
;   hyphen                  U+002D                    ES
;   comma                   U+002C                    CS
;   percent sign            U+0025                    ET
;   asterisk                U+002A                    ON
;   parentheses             U+0028, U+0029            ON, paired brackets
;   square brackets         U+005B, U+005D            ON, paired brackets
;   less-than, greater-than U+003C, U+003E            ON, mirrored
;   sheva (a Hebrew point)  U+05B0                    NSM
;
; In each example of the first group the name satisfies the wide rule,
; the display that BIDI-NAME-DISPLAY computes
; is the display of the algorithm
; in a paragraph from left to right, and the way back gives the name.

(defmacro bidi-rule-display-example (name display)
  `(assert-event
    (b* ((name ,name)
         (display ,display))
      (and (bidi-rule-wide-p name *v17*)
           (equal (bidi-name-display name *v17*) display)
           (equal (bidi-display name *ltr* *v17*) display)
           (equal (bidi-name-read display *v17*) name)))))

; The example of the documentation:
; asterisk, sheva, alef, 1, comma, 2, hyphen, bet, hyphen, percent sign.
; The first part is the asterisk with the sheva, the last part
; is the hyphen and the percent sign, and the number 1,2 keeps its order.

(bidi-rule-display-example
 '(#x2A #x5B0 #x5D0 #x31 #x2C #x32 #x2D #x5D1 #x2D #x25)
 '(#x2A #x5B0 #x5D1 #x2D #x31 #x2C #x32 #x5D0 #x2D #x25))

; A name without a right-to-left letter is displayed as it is stored.

(bidi-rule-display-example '(#x31 #x2D #x32)
                           '(#x31 #x2D #x32))

; The hyphen joins two European digits into one number after alef,
; but not after an Arabic letter, where they count as Arabic digits;
; the comma joins them in both cases.

(bidi-rule-display-example '(#x5D0 #x31 #x2D #x32)
                           '(#x31 #x2D #x32 #x5D0))

(bidi-rule-display-example '(#x627 #x31 #x2D #x32)
                           '(#x32 #x2D #x31 #x627))

(bidi-rule-display-example '(#x627 #x31 #x2C #x32)
                           '(#x31 #x2C #x32 #x627))

; A mirrored character of the middle part is replaced.

(bidi-rule-display-example '(#x5D0 #x3C #x5D1)
                           '(#x5D1 #x3E #x5D0))

; A bracket pair with a digit inside is in the middle part;
; one with only an asterisk inside is not, and stays where it is.

(bidi-rule-display-example '(#x5D0 #x28 #x31 #x29 #x2A)
                           '(#x28 #x31 #x29 #x5D0 #x2A))

(bidi-rule-display-example '(#x5D0 #x28 #x2A #x29 #x2A)
                           '(#x5D0 #x28 #x2A #x29 #x2A))

; Brackets that do not match: the square brackets are not a pair,
; because the parenthesis between them is closed after them
; [UAX #9, BD16].

(bidi-rule-display-example '(#x5D0 #x5B #x28 #x31 #x5D #x29)
                           '(#x5B #x31 #x29 #x5D #x5D0 #x29))

; Marks: each stays after the character that it follows in the name.

(bidi-rule-display-example '(#x5D0 #x28 #x5B0 #x31 #x29 #x5B0 #x2D)
                           '(#x28 #x5B0 #x31 #x29 #x5B0 #x5D0 #x2D))

;;;;;;;;;;;;;;;;;;;;

; The levels and the classes after the weak rules,
; computed without the rules of the algorithm
; (BIDI-NAME-LEVELS, and BIDI-CLUSTERS-WEAK-CLASSES
; of the book bidi-rule-display-weak.lisp, which the algorithm loads).
; In each example the name satisfies the wide rule,
; and the levels and the classes are those of the algorithm
; in a paragraph from left to right.

(defmacro bidi-rule-levels-example (name levels kinds)
  `(assert-event
    (b* ((name ,name)
         (chars (code-points-to-bidi-chars name *v17*))
         (classes (bidi-clusters-weak-classes (bidi-clusters name *v17*)
                                              nil
                                              nil
                                              *v17*)))
      (and (bidi-rule-wide-p name *v17*)
           (equal (bidi-name-levels name *v17*) ,levels)
           (equal (bidi-paragraph-all-levels chars 0) ,levels)
           (equal (bidi-class-list-kinds classes) ,kinds)
           (equal (bidi-resolve-weak-types (bidi-char-list-classes chars)
                                           (bidi-class-left-to-right))
                  classes)))))

(define bidi-class-list-kinds ((classes bidi-class-listp))
  :returns (kinds symbol-listp)
  (if (endp classes)
      nil
    (cons (bidi-class-kind (car classes))
          (bidi-class-list-kinds (cdr classes))))
  :hooks nil)

; The example of the documentation.  The sheva is a mark of the cluster
; of the asterisk; the comma joins the two digits, the hyphens do not.

(bidi-rule-levels-example
 '(#x2A #x5B0 #x5D0 #x31 #x2C #x32 #x2D #x5D1 #x2D #x25)
 '(0 0 1 2 2 2 1 1 0 0)
 '(:other-neutral :other-neutral :right-to-left
   :european-number :european-number :european-number
   :other-neutral :right-to-left :other-neutral :other-neutral))

; After an Arabic letter the European digits count as Arabic digits,
; and the hyphen does not join them.

(bidi-rule-levels-example '(#x627 #x31 #x2D #x32)
                          '(1 2 1 2)
                          '(:right-to-left :arabic-number
                            :other-neutral :arabic-number))

; A sheva at the start of the name gets the class L.
; A bracket pair with a digit inside is in the middle part;
; one with nothing but an asterisk inside is after it.

(bidi-rule-levels-example '(#x5B0 #x5D0 #x28 #x31 #x29 #x2A)
                          '(0 1 1 2 1 0)
                          '(:left-to-right :right-to-left :other-neutral
                            :european-number :other-neutral :other-neutral))

(bidi-rule-levels-example '(#x5D0 #x28 #x2A #x29)
                          '(1 0 0 0)
                          '(:right-to-left :other-neutral
                            :other-neutral :other-neutral))

; A comma with a mark is not alone in its cluster and joins nothing.

(bidi-rule-levels-example '(#x5D0 #x31 #x2C #x5B0 #x32)
                          '(1 2 1 1 2)
                          '(:right-to-left :european-number :other-neutral
                            :other-neutral :european-number))

;;;;;;;;;;;;;;;;;;;;

; Names that do not satisfy the wide rule,
; for which the display that BIDI-NAME-DISPLAY computes
; is not the display of the algorithm.

; A terminator next to a European digit: the algorithm makes it
; a part of the number [UAX #9, rule W5].

(assert-event
 (b* ((name '(#x5D0 #x31 #x25)))
   (and (not (bidi-rule-wide-p name *v17*))
        (equal (bidi-display name *ltr* *v17*) '(#x31 #x25 #x5D0))
        (equal (bidi-name-display name *v17*) '(#x31 #x5D0 #x25)))))

; A letter of class L: the digit after it takes its direction
; [UAX #9, rule W7].

(assert-event
 (b* ((name '(#x5D0 #x61 #x31)))
   (and (not (bidi-rule-wide-p name *v17*))
        (equal (bidi-display name *ltr* *v17*) '(#x5D0 #x61 #x31))
        (equal (bidi-name-display name *v17*) '(#x31 #x61 #x5D0)))))

; A bracket before the first letter: the pair takes the direction
; of the paragraph [UAX #9, rule N0].

(assert-event
 (b* ((name '(#x28 #x5D0 #x29)))
   (and (not (bidi-rule-wide-p name *v17*))
        (equal (bidi-display name *ltr* *v17*) '(#x28 #x5D0 #x29))
        (equal (bidi-name-display name *v17*) '(#x28 #x28 #x5D0)))))

; Two names with both European and Arabic digits,
; which satisfy the other conditions of the wide rule.
; They are displayed alike, by the algorithm and by BIDI-NAME-DISPLAY,
; so the way back cannot give both: it gives the second.

(assert-event
 (b* ((name1 '(#x5D0 #x31 #x2D #x661 #x31))
      (name2 '(#x5D0 #x661 #x31 #x2D #x31))
      (display '(#x661 #x31 #x2D #x31 #x5D0)))
   (and (not (bidi-rule-wide-p name1 *v17*))
        (not (bidi-rule-wide-p name2 *v17*))
        (equal (bidi-display name1 *ltr* *v17*) display)
        (equal (bidi-display name2 *ltr* *v17*) display)
        (equal (bidi-name-display name1 *v17*) display)
        (equal (bidi-name-display name2 *v17*) display)
        (equal (bidi-name-read display *v17*) name2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The search.
;
; Go through the lists of a length, from an index on.
; Count the names (the lists that the keyword selects:
; see BIDI-RULE-TEST-LABEL-P in the tests of the Bidi Rule),
; and those among them for which the display of BIDI-NAME-DISPLAY
; is not the display of the algorithm in a paragraph from left to right,
; or for which the way back does not give the name.

(define bidi-rule-display-test-search ((index natp)
                                       (count natp)
                                       (length natp)
                                       (characters code-point-listp)
                                       (rule keywordp)
                                       (ver versionp)
                                       (names natp)
                                       (differ natp))
  :returns (mv (new-names natp :rule-classes :type-prescription)
               (new-differ natp :rule-classes :type-prescription))
  (b* ((index (lnfix index))
       (count (lnfix count))
       (names (lnfix names))
       (differ (lnfix differ))
       ((when (>= index count)) (mv names differ))
       (cps (bidi-rule-test-text index length characters))
       ((unless (bidi-rule-test-label-p cps rule ver))
        (bidi-rule-display-test-search (+ 1 index) count length characters
                                       rule ver names differ))
       (display (bidi-display cps *ltr* ver))
       (same (and (equal (bidi-name-display cps ver) display)
                  (equal (bidi-name-read display ver) cps))))
    (bidi-rule-display-test-search (+ 1 index) count length characters
                                   rule ver
                                   (+ 1 names)
                                   (if same differ (+ 1 differ))))
  :measure (nfix (- (nfix count) (nfix index)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks nil)

; All the lists of a length.

(define bidi-rule-display-test ((length natp)
                                (characters code-point-listp)
                                (rule keywordp)
                                (ver versionp))
  :returns (mv (names natp :rule-classes :type-prescription)
               (differ natp :rule-classes :type-prescription))
  (bidi-rule-display-test-search 0
                                 (expt (len characters) (lnfix length))
                                 length
                                 characters
                                 rule
                                 ver
                                 0
                                 0)
  :hooks nil)

; In each test below, the first number is how many lists of the length
; are names that the search checks, and the second is how many of those
; fail the check.

(defmacro bidi-rule-display-test-is (length characters rule ver
                                            names differ)
  `(assert-event
    (mv-let (names differ)
        (bidi-rule-display-test ,length ,characters ,rule ,ver)
      (and (equal names ,names)
           (equal differ ,differ)))))

;;;;;;;;;;;;;;;;;;;;

; The sixteen characters of the search for the wide rule
; (see the tests of the Bidi Rule): the right-to-left names
; that satisfy the wide rule, up to five characters.
; There are 318,375 of them.
; The same check for six characters, 4,437,669 names and none that fails,
; was run once, on 2026-11-25, outside the certified books.

(bidi-rule-display-test-is 1 *bidi-rule-test-wide-characters* :wide *v17*
                           3 0)
(bidi-rule-display-test-is 2 *bidi-rule-test-wide-characters* :wide *v17*
                           69 0)
(bidi-rule-display-test-is 3 *bidi-rule-test-wide-characters* :wide *v17*
                           1215 0)
(bidi-rule-display-test-is 4 *bidi-rule-test-wide-characters* :wide *v17*
                           19455 0)
(bidi-rule-display-test-is 5 *bidi-rule-test-wide-characters* :wide *v17*
                           297633 0)

; For 16.0.0 and 18.0.0, up to four characters.

(bidi-rule-display-test-is 4 *bidi-rule-test-wide-characters* :wide
                           (version-v16.0.0) 19455 0)
(bidi-rule-display-test-is 4 *bidi-rule-test-wide-characters* :wide
                           (version-v18.0.0) 19455 0)

;;;;;;;;;;;;;;;;;;;;

; The twelve characters with letters of class L
; (see the tests of the Bidi Rule): all the names
; that satisfy the wide rule, left-to-right and right-to-left,
; up to five characters.
; The same check for six characters, 816,451 names and none that fails,
; was run once, on 2026-11-25, outside the certified books.

(bidi-rule-display-test-is 1 *bidi-rule-test-mixed-terminator-characters*
                           :wide-all *v17* 11 0)
(bidi-rule-display-test-is 2 *bidi-rule-test-mixed-terminator-characters*
                           :wide-all *v17* 111 0)
(bidi-rule-display-test-is 3 *bidi-rule-test-mixed-terminator-characters*
                           :wide-all *v17* 1063 0)
(bidi-rule-display-test-is 4 *bidi-rule-test-mixed-terminator-characters*
                           :wide-all *v17* 9887 0)
(bidi-rule-display-test-is 5 *bidi-rule-test-mixed-terminator-characters*
                           :wide-all *v17* 90351 0)

;;;;;;;;;;;;;;;;;;;;

; Eleven characters with two kinds of brackets:
; alef (R); Arabic alef (AL); 1 (EN); Arabic-Indic one (AN); comma (CS);
; asterisk, the two parentheses and the two square brackets (ON);
; sheva (NSM).
; The right-to-left names that satisfy the wide rule,
; up to five characters.
; The same check for six characters, 394,108 names and none that fails,
; was run once, on 2026-11-25, outside the certified books.

(defconst *bidi-rule-display-test-bracket-characters*
  '(#x5D0 #x627 #x31 #x661 #x2C #x2A #x28 #x29 #x5B #x5D #x5B0))

(bidi-rule-display-test-is 1 *bidi-rule-display-test-bracket-characters*
                           :wide *v17* 2 0)
(bidi-rule-display-test-is 2 *bidi-rule-display-test-bracket-characters*
                           :wide *v17* 28 0)
(bidi-rule-display-test-is 3 *bidi-rule-display-test-bracket-characters*
                           :wide *v17* 322 0)
(bidi-rule-display-test-is 4 *bidi-rule-display-test-bracket-characters*
                           :wide *v17* 3508 0)
(bidi-rule-display-test-is 5 *bidi-rule-display-test-bracket-characters*
                           :wide *v17* 37402 0)
