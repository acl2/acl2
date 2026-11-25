; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Tests of the Bidi Rule [RFC 5893, Section 2]
; and of the two rules derived from it (book bidi-rule.lisp).
;
; The first part has examples of labels and of domain names.
;
; The second part is about labels that are displayed alike.
; That the strict rule and the wide rule keep
; two different labels from being displayed alike is not proved:
; what is known is here.  For the Bidi Rule as it is written,
; and for the wide rule with each of its conditions dropped in turn,
; there are two labels that are displayed alike.
; For the strict rule and for the wide rule, a search finds none:
; it runs the Unicode Bidirectional Algorithm on every list,
; up to a length, of the characters of a small set,
; and compares the displays of the lists that satisfy the rule.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../bidi-rule")
(include-book "../bidirectional-algorithm")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic-5/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro test (form)
  `(assert-event ,form))

(defconst *v17* (version-v17.0.0))

(defconst *ltr* (paragraph-direction-left-to-right))

(defconst *rtl* (paragraph-direction-right-to-left))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples of the Bidi Rule.
;
; The characters, with their classes:
;   a, b                    U+0061, U+0062            L
;   alef, bet               U+05D0, U+05D1 (Hebrew)   R
;   Arabic alef             U+0627                    AL
;   Thaana haa              U+0780                    AL
;   1, 2                    U+0031, U+0032            EN
;   Arabic-Indic one, two   U+0661, U+0662            AN
;   hyphen-minus            U+002D                    ES
;   comma                   U+002C                    CS
;   percent sign            U+0025                    ET
;   asterisk                U+002A                    ON
;   parentheses             U+0028, U+0029            ON, paired brackets
;   less-than, greater-than U+003C, U+003E            ON, mirrored
;   Hebrew point sheva      U+05B0                    NSM
;   Thaana abafili          U+07A6                    NSM
;   zero width non-joiner   U+200C                    BN
;   space                   U+0020                    WS

; Right-to-left labels that satisfy the rule.

(test (bidi-rule-p '(#x5D0 #x5D1) *v17*))
(test (bidi-rule-p '(#x627 #x661 #x662) *v17*))
(test (bidi-rule-p '(#x5D0 #x2D #x5D1 #x31) *v17*))
(test (bidi-rule-p '(#x5D0 #x25 #x2A #x2C #x5D1) *v17*))

; A label can end with nonspacing marks after a letter or a digit
; (condition 3).  Thaana words end with a mark, and are
; one of the reasons that [RFC 5893] gives for the rule (Section 4.1).

(test (bidi-rule-p '(#x780 #x7A6) *v17*))
(test (bidi-rule-p '(#x5D0 #x31 #x5B0 #x5B0) *v17*))

; Left-to-right labels that satisfy the rule.

(test (bidi-rule-p '(#x61 #x62) *v17*))
(test (bidi-rule-p '(#x61 #x2D #x31) *v17*))
(test (bidi-rule-p '(#x61 #x25 #x62) *v17*))

; Labels that fail one condition.

; Condition 1: the first character is not of class L, R or AL.
(test (not (bidi-rule-p nil *v17*)))
(test (not (bidi-rule-p '(#x31 #x61) *v17*)))
(test (not (bidi-rule-p '(#x31 #x5D0) *v17*)))
(test (not (bidi-rule-p '(#x661 #x627) *v17*)))
(test (not (bidi-rule-p '(#x2D #x61) *v17*)))

; Condition 2: a right-to-left label with a character of class L,
; or with a space.
(test (not (bidi-rule-p '(#x5D0 #x61 #x5D1) *v17*)))
(test (not (bidi-rule-p '(#x5D0 #x20 #x5D1) *v17*)))

; Condition 3: a right-to-left label that ends with a hyphen,
; and one that ends with a mark after a hyphen.
(test (not (bidi-rule-p '(#x5D0 #x2D) *v17*)))
(test (not (bidi-rule-p '(#x5D0 #x2D #x5B0) *v17*)))

; Condition 4: a right-to-left label with digits of the two kinds.
(test (not (bidi-rule-p '(#x5D0 #x31 #x661) *v17*)))

; Condition 5: a left-to-right label with a right-to-left letter,
; or with an Arabic-Indic digit.
(test (not (bidi-rule-p '(#x61 #x5D0) *v17*)))
(test (not (bidi-rule-p '(#x61 #x661) *v17*)))

; Condition 6: a left-to-right label that ends with a hyphen.
(test (not (bidi-rule-p '(#x61 #x2D) *v17*)))

; The two ways of saying which labels are right-to-left labels:
; by the whole label, and by its first character.
; The second label below has a character of class AN after a first
; character of class L; it does not satisfy the rule.

(test (bidi-right-to-left-label-p '(#x5D0 #x31) *v17*))
(test (bidi-right-to-left-label-p '(#x61 #x661) *v17*))
(test (not (bidi-right-to-left-label-p '(#x61 #x31) *v17*)))

; Domain names.  A domain name with no right-to-left label
; passes the check whatever its labels are;
; in a Bidi domain name every label must satisfy the rule,
; the left-to-right ones too.

(test (not (bidi-domain-name-p '((#x31 #x61) (#x62)) *v17*)))
(test (bidi-rule-domain-name-p '((#x31 #x61) (#x62)) *v17*))
(test (bidi-domain-name-p '((#x5D0 #x5D1) (#x62)) *v17*))
(test (bidi-rule-domain-name-p '((#x5D0 #x5D1) (#x62)) *v17*))
(test (bidi-rule-domain-name-p '((#x5D0 #x5D1) (#x61 #x31)) *v17*))
(test (not (bidi-rule-domain-name-p '((#x5D0 #x5D1) (#x31 #x61)) *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Labels that satisfy the Bidi Rule and are displayed alike.

; With a European terminator.  In alef, 1, hyphen, percent, 1
; the hyphen stands between a digit and the percent sign,
; so it does not join two numbers [UAX #9, rule W4];
; the percent sign then joins the digit after it [UAX #9, rule W5],
; and the label has the two numbers 1 and %1.
; In alef, percent, 1, hyphen, 1 the hyphen stands between two digits
; and joins them, and the percent sign joins that number:
; the label has the one number %1-1.
; Both labels are displayed as percent, 1, hyphen, 1, alef,
; in a paragraph of either direction.

(defconst *terminator-1* '(#x5D0 #x31 #x2D #x25 #x31))
(defconst *terminator-2* '(#x5D0 #x25 #x31 #x2D #x31))

(test (bidi-rule-p *terminator-1* *v17*))
(test (bidi-rule-p *terminator-2* *v17*))
(test (not (bidi-rule-strict-p *terminator-1* *v17*)))
(test (not (bidi-rule-strict-p *terminator-2* *v17*)))
(test (equal (bidi-display *terminator-1* *ltr* *v17*)
             '(#x25 #x31 #x2D #x31 #x5D0)))
(test (equal (bidi-display *terminator-2* *ltr* *v17*)
             '(#x25 #x31 #x2D #x31 #x5D0)))
(test (equal (bidi-display *terminator-1* *rtl* *v17*)
             '(#x25 #x31 #x2D #x31 #x5D0)))
(test (equal (bidi-display *terminator-2* *rtl* *v17*)
             '(#x25 #x31 #x2D #x31 #x5D0)))

; The same with the euro sign U+20AC, the degree sign U+00B0
; and the Arabic percent sign U+066A, which are of class ET too.

(test (equal (bidi-display '(#x5D0 #x31 #x2D #x20AC #x31) *ltr* *v17*)
             (bidi-display '(#x5D0 #x20AC #x31 #x2D #x31) *ltr* *v17*)))
(test (equal (bidi-display '(#x5D0 #x31 #x2D #xB0 #x31) *ltr* *v17*)
             (bidi-display '(#x5D0 #xB0 #x31 #x2D #x31) *ltr* *v17*)))
(test (equal (bidi-display '(#x5D0 #x31 #x2D #x66A #x31) *ltr* *v17*)
             (bidi-display '(#x5D0 #x66A #x31 #x2D #x31) *ltr* *v17*)))

; With a boundary neutral.  The zero width non-joiner is displayed
; at the level of the character before it:
; after the digit it stays after the digit,
; and after the first alef it is moved with that alef,
; to the left of the alef and so again after the digit.

(defconst *boundary-neutral-1* '(#x5D0 #x31 #x200C #x5D0))
(defconst *boundary-neutral-2* '(#x5D0 #x200C #x31 #x5D0))

(test (bidi-rule-p *boundary-neutral-1* *v17*))
(test (bidi-rule-p *boundary-neutral-2* *v17*))
(test (not (bidi-rule-strict-p *boundary-neutral-1* *v17*)))
(test (not (bidi-rule-strict-p *boundary-neutral-2* *v17*)))
(test (equal (bidi-display *boundary-neutral-1* *ltr* *v17*)
             '(#x5D0 #x31 #x200C #x5D0)))
(test (equal (bidi-display *boundary-neutral-2* *ltr* *v17*)
             '(#x5D0 #x31 #x200C #x5D0)))
(test (equal (bidi-display *boundary-neutral-1* *rtl* *v17*)
             (bidi-display *boundary-neutral-2* *rtl* *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Examples of the strict rule and of the wide rule.

; Labels that satisfy the strict rule satisfy the wide rule
; (a theorem of the library).

(test (bidi-rule-strict-p '(#x5D0 #x2D #x5D1 #x31) *v17*))
(test (bidi-rule-wide-p '(#x5D0 #x2D #x5D1 #x31) *v17*))
(test (bidi-rule-strict-p '(#x61 #x2D #x31) *v17*))
(test (bidi-rule-wide-p '(#x61 #x2D #x31) *v17*))

; Right-to-left names that satisfy the wide rule and not the Bidi Rule:
; asterisk, alef, bet, asterisk; alef, bet, hyphen;
; percent, alef, bet; alef, percent, hyphen, 1 (the terminator
; is not next to the digit).

(test (bidi-rule-wide-p '(#x2A #x5D0 #x5D1 #x2A) *v17*))
(test (not (bidi-rule-p '(#x2A #x5D0 #x5D1 #x2A) *v17*)))
(test (bidi-rule-wide-p '(#x5D0 #x5D1 #x2D) *v17*))
(test (not (bidi-rule-p '(#x5D0 #x5D1 #x2D) *v17*)))
(test (bidi-rule-wide-p '(#x25 #x5D0 #x5D1) *v17*))
(test (bidi-rule-wide-p '(#x5D0 #x25 #x2D #x31) *v17*))

; Their displays, in a paragraph from left to right:
; the punctuation at the two ends stays where it is.

(test (equal (bidi-display '(#x2A #x5D0 #x5D1 #x2A) *ltr* *v17*)
             '(#x2A #x5D1 #x5D0 #x2A)))
(test (equal (bidi-display '(#x5D0 #x5D1 #x2D) *ltr* *v17*)
             '(#x5D1 #x5D0 #x2D)))

; Left-to-right names have only the condition on the classes,
; and are displayed as they are stored.

(test (bidi-rule-wide-p '(#x2A #x61 #x25 #x31 #x2D) *v17*))
(test (not (bidi-rule-p '(#x2A #x61 #x25 #x31 #x2D) *v17*)))
(test (equal (bidi-display '(#x2A #x61 #x25 #x31 #x2D) *ltr* *v17*)
             '(#x2A #x61 #x25 #x31 #x2D)))
(test (not (bidi-rule-wide-p '(#x61 #x20 #x62) *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Each condition of the wide rule for a right-to-left name is needed:
; for each one there are two names that are displayed alike,
; in a paragraph from left to right,
; of which at least one fails that condition and no other.

; The conditions for a right-to-left name, one by one:
; the classes; no character of class L; not both EN and AN;
; the start; no terminator next to a European digit.

(define bidi-rule-test-wide-conditions ((name code-point-listp)
                                        (ver versionp))
  :returns (conditions boolean-listp)
  (list (bidi-rule-wide-code-points-p name ver)
        (not (bidi-class-kind-present-p :left-to-right name ver))
        (not (and (bidi-class-kind-present-p :european-number name ver)
                  (bidi-class-kind-present-p :arabic-number name ver)))
        (bidi-rule-wide-start-p name ver)
        (not (bidi-terminator-next-to-digit-p (bidi-drop-marks name ver)
                                              ver)))
  :hooks nil)

; Check that two names are displayed alike
; in a paragraph from left to right.

(define bidi-rule-test-alike ((name1 code-point-listp)
                              (name2 code-point-listp)
                              (ver versionp))
  :returns (yes/no booleanp)
  (equal (bidi-display name1 (paragraph-direction-left-to-right) ver)
         (bidi-display name2 (paragraph-direction-left-to-right) ver))
  :hooks nil)

; No character of class L: alef, a, 1, alef and alef, a, alef, 1.
; In the first the digit follows a and is displayed with it,
; from left to right; in the second it follows alef
; and is displayed to the left of that alef, so again after a.

(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x61 #x31 #x5D0) *v17*)
             '(t nil t t t)))
(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x61 #x5D0 #x31) *v17*)
             '(t nil t t t)))
(test (bidi-rule-test-alike '(#x5D0 #x61 #x31 #x5D0)
                            '(#x5D0 #x61 #x5D0 #x31)
                            *v17*))

; Not both EN and AN: alef, 1, hyphen, Arabic-Indic one, 1
; and alef, Arabic-Indic one, 1, hyphen, 1.

(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x31 #x2D #x661 #x31)
                                             *v17*)
             '(t t nil t t)))
(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x661 #x31 #x2D #x31)
                                             *v17*)
             '(t t nil t t)))
(test (bidi-rule-test-alike '(#x5D0 #x31 #x2D #x661 #x31)
                            '(#x5D0 #x661 #x31 #x2D #x31)
                            *v17*))

; No digit before the first right-to-left letter: 1, alef and alef, 1.
; The second satisfies the wide rule.

(test (equal (bidi-rule-test-wide-conditions '(#x31 #x5D0) *v17*)
             '(t t t nil t)))
(test (bidi-rule-wide-p '(#x5D0 #x31) *v17*))
(test (bidi-rule-test-alike '(#x31 #x5D0) '(#x5D0 #x31) *v17*))

; No paired bracket before the first right-to-left letter:
; (, alef, (, alef and (, alef, ), alef.
; In the second the two parentheses are a pair,
; which takes the direction of the paragraph;
; in the first the second parenthesis is displayed as its mirror image.

(test (equal (bidi-rule-test-wide-conditions '(#x28 #x5D0 #x28 #x5D0) *v17*)
             '(t t t nil t)))
(test (equal (bidi-rule-test-wide-conditions '(#x28 #x5D0 #x29 #x5D0) *v17*)
             '(t t t nil t)))
(test (bidi-rule-test-alike '(#x28 #x5D0 #x28 #x5D0)
                            '(#x28 #x5D0 #x29 #x5D0)
                            *v17*))
(test (equal (bidi-display '(#x28 #x5D0 #x28 #x5D0) *ltr* *v17*)
             '(#x28 #x5D0 #x29 #x5D0)))

; A bracket after the first letter is allowed,
; and so is a mirrored character that is not a paired bracket
; before it.

(test (bidi-rule-wide-p '(#x5D0 #x28 #x5D0 #x29) *v17*))
(test (bidi-rule-wide-p '(#x3C #x5D0 #x3E) *v17*))

; No terminator next to a European digit:
; percent, alef, 1 and alef, percent, 1.

(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x25 #x31) *v17*)
             '(t t t t nil)))
(test (bidi-rule-wide-p '(#x25 #x5D0 #x31) *v17*))
(test (bidi-rule-test-alike '(#x25 #x5D0 #x31) '(#x5D0 #x25 #x31) *v17*))

; The nonspacing marks are left out in that condition:
; percent, sheva, alef, 1 and alef, percent, sheva, 1.
; In the second the mark takes the class of the percent sign,
; and both join the digit.

(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x25 #x5B0 #x31) *v17*)
             '(t t t t nil)))
(test (bidi-rule-wide-p '(#x25 #x5B0 #x5D0 #x31) *v17*))
(test (bidi-rule-test-alike '(#x25 #x5B0 #x5D0 #x31)
                            '(#x5D0 #x25 #x5B0 #x31)
                            *v17*))

; No character of class BN, which is the condition on the classes:
; zero width non-joiner, alef, hyphen and alef, non-joiner, hyphen.

(test (equal (bidi-rule-test-wide-conditions '(#x200C #x5D0 #x2D) *v17*)
             '(nil t t t t)))
(test (equal (bidi-rule-test-wide-conditions '(#x5D0 #x200C #x2D) *v17*)
             '(nil t t t t)))
(test (bidi-rule-test-alike '(#x200C #x5D0 #x2D) '(#x5D0 #x200C #x2D) *v17*))

; The wide rule is for a paragraph from left to right.
; In a paragraph from right to left,
; sheva, alef and alef, sheva satisfy it and are displayed alike.

(test (bidi-rule-wide-p '(#x5B0 #x5D0) *v17*))
(test (bidi-rule-wide-p '(#x5D0 #x5B0) *v17*))
(test (equal (bidi-display '(#x5B0 #x5D0) *rtl* *v17*)
             (bidi-display '(#x5D0 #x5B0) *rtl* *v17*)))
(test (not (bidi-rule-test-alike '(#x5B0 #x5D0) '(#x5D0 #x5B0) *v17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The search.

; The list of a given length, of the characters of a set,
; that has a given index: the index is read as a number
; in the base that is the number of the characters.

(define bidi-rule-test-text ((index natp)
                             (length natp)
                             (characters code-point-listp))
  :returns (cps code-point-listp)
  (b* (((when (zp length)) nil)
       (index (lnfix index))
       (base (len characters))
       ((when (= base 0)) nil)
       (cp (nth (mod index base) characters))
       (cp (if (code-point-p cp) cp 0)))
    (cons cp
          (bidi-rule-test-text (floor index base) (- length 1) characters)))
  :hooks nil)

; A list of characters of the set as a number:
; the position of each character in the set, from 1,
; is a digit in a base larger than the number of the characters.
; Two different lists of the same length have different numbers.

(define bidi-rule-test-position ((cp code-point-p)
                                 (characters code-point-listp))
  :returns (position natp :rule-classes :type-prescription)
  (b* (((when (endp characters)) 0)
       ((when (equal (code-point-fix cp)
                     (code-point-fix (car characters))))
        1)
       (position (bidi-rule-test-position cp (cdr characters))))
    (if (= position 0)
        0
      (+ 1 position)))
  :hooks nil)

(define bidi-rule-test-number ((cps code-point-listp)
                               (characters code-point-listp)
                               (number natp))
  :returns (new-number natp :rule-classes :type-prescription)
  (b* (((when (endp cps)) (lnfix number)))
    (bidi-rule-test-number (cdr cps)
                           characters
                           (+ (* (+ 2 (len characters)) (lnfix number))
                              (bidi-rule-test-position (car cps)
                                                       characters))))
  :hooks nil)

; The labels that the search compares.
; For the first three keywords they are the right-to-left labels
; that satisfy one of the three rules:
; a left-to-right label that satisfies one of them
; is displayed as it is stored in a paragraph from left to right
; (see the theorems of the library),
; and the sets of characters are chosen for the right-to-left labels.
; For the last two keywords they are all the labels that satisfy
; the strict rule or the wide rule, of the two kinds;
; those searches are run on a set of characters that has letters
; of class L.

(define bidi-rule-test-label-p ((cps code-point-listp)
                                (rule keywordp)
                                (ver versionp))
  :returns (yes/no booleanp)
  (case rule
    (:rule (and (bidi-right-to-left-label-p cps ver)
                (bidi-rule-p cps ver)))
    (:strict (and (bidi-right-to-left-label-p cps ver)
                  (bidi-rule-strict-p cps ver)))
    (:wide (and (bidi-right-to-left-label-p cps ver)
                (bidi-rule-wide-p cps ver)))
    (:strict-all (bidi-rule-strict-p cps ver))
    (:wide-all (bidi-rule-wide-p cps ver))
    (otherwise nil))
  :hooks nil)

; Go through the lists of a length, from an index on.
; The table has the displays, as numbers, of the labels seen so far.
; Count the labels, and those among them whose display
; is the display of a label seen before.

(define bidi-rule-test-search ((index natp)
                               (count natp)
                               (length natp)
                               (characters code-point-listp)
                               (rule keywordp)
                               (direction paragraph-direction-p)
                               (ver versionp)
                               table
                               (labels natp)
                               (alike natp))
  :returns (mv (new-labels natp :rule-classes :type-prescription)
               (new-alike natp :rule-classes :type-prescription))
  (b* ((index (lnfix index))
       (count (lnfix count))
       (labels (lnfix labels))
       (alike (lnfix alike))
       ((when (>= index count))
        (b* ((- (fast-alist-free table)))
          (mv labels alike)))
       (cps (bidi-rule-test-text index length characters))
       ((unless (bidi-rule-test-label-p cps rule ver))
        (bidi-rule-test-search (+ 1 index) count length characters
                               rule direction ver table labels alike))
       (display (bidi-display cps direction ver))
       (key (bidi-rule-test-number display characters 0))
       ((when (hons-get key table))
        (bidi-rule-test-search (+ 1 index) count length characters
                               rule direction ver table
                               (+ 1 labels) (+ 1 alike)))
       (table (hons-acons key t table)))
    (bidi-rule-test-search (+ 1 index) count length characters
                           rule direction ver table
                           (+ 1 labels) alike))
  :measure (nfix (- (nfix count) (nfix index)))
  :hints (("Goal" :in-theory (enable nfix fix natp o-p o-finp o<)))
  :hooks nil)

; All the lists of a length.

(define bidi-rule-test ((length natp)
                        (characters code-point-listp)
                        (rule keywordp)
                        (direction paragraph-direction-p)
                        (ver versionp))
  :returns (mv (labels natp :rule-classes :type-prescription)
               (alike natp :rule-classes :type-prescription))
  (bidi-rule-test-search 0
                         (expt (len characters) (lnfix length))
                         length
                         characters
                         rule
                         direction
                         ver
                         nil
                         0
                         0)
  :hooks nil)

; In each test below, the first number is how many lists of the length
; are labels that the search compares,
; and the second is how many of those
; are displayed like one that comes before.

(defmacro bidi-rule-test-is (length characters rule direction ver
                                    labels alike)
  `(assert-event
    (mv-let (labels alike)
        (bidi-rule-test ,length ,characters ,rule ,direction ,ver)
      (and (equal labels ,labels)
           (equal alike ,alike)))))

;;;;;;;;;;;;;;;;;;;;

; Thirteen characters, one or two of each class that the strict rule
; allows in a right-to-left label: alef, bet (R); Arabic alef (AL);
; 1, 2 (EN); Arabic-Indic one, two (AN); hyphen (ES); comma (CS);
; asterisk and the two parentheses (ON); sheva (NSM).
; The set has the mirror image of each of its characters,
; so the display of a list of them is a list of them.

(defconst *bidi-rule-test-strict-characters*
  '(#x5D0 #x5D1 #x627 #x31 #x32 #x661 #x662 #x2D #x2C #x2A #x28 #x29 #x5B0))

; The strict rule: no two labels are displayed alike,
; in a paragraph of either direction.
; The same search for six characters, 416,724 labels
; and none displayed like another in either direction,
; was run once, on 2026-11-24, outside the certified books.

(bidi-rule-test-is 1 *bidi-rule-test-strict-characters* :strict *ltr* *v17*
                   3 0)
(bidi-rule-test-is 2 *bidi-rule-test-strict-characters* :strict *ltr* *v17*
                   24 0)
(bidi-rule-test-is 3 *bidi-rule-test-strict-characters* :strict *ltr* *v17*
                   273 0)
(bidi-rule-test-is 4 *bidi-rule-test-strict-characters* :strict *ltr* *v17*
                   3174 0)
(bidi-rule-test-is 5 *bidi-rule-test-strict-characters* :strict *ltr* *v17*
                   36543 0)

(bidi-rule-test-is 1 *bidi-rule-test-strict-characters* :strict *rtl* *v17*
                   3 0)
(bidi-rule-test-is 2 *bidi-rule-test-strict-characters* :strict *rtl* *v17*
                   24 0)
(bidi-rule-test-is 3 *bidi-rule-test-strict-characters* :strict *rtl* *v17*
                   273 0)
(bidi-rule-test-is 4 *bidi-rule-test-strict-characters* :strict *rtl* *v17*
                   3174 0)
(bidi-rule-test-is 5 *bidi-rule-test-strict-characters* :strict *rtl* *v17*
                   36543 0)

; For 16.0.0 and 18.0.0, up to four characters.

(bidi-rule-test-is 4 *bidi-rule-test-strict-characters* :strict *ltr*
                   (version-v16.0.0) 3174 0)
(bidi-rule-test-is 4 *bidi-rule-test-strict-characters* :strict *ltr*
                   (version-v18.0.0) 3174 0)

;;;;;;;;;;;;;;;;;;;;

; The Bidi Rule as it is written, with the percent sign (ET) added
; to the thirteen characters: among the labels of five characters,
; sixteen are displayed like another, in either direction;
; there are none among the shorter ones.

(defconst *bidi-rule-test-terminator-characters*
  (append *bidi-rule-test-strict-characters* '(#x25)))

(bidi-rule-test-is 4 *bidi-rule-test-terminator-characters* :rule *ltr* *v17*
                   3714 0)
(bidi-rule-test-is 5 *bidi-rule-test-terminator-characters* :rule *ltr* *v17*
                   46554 16)
(bidi-rule-test-is 5 *bidi-rule-test-terminator-characters* :rule *rtl* *v17*
                   46554 16)

; The strict rule on the same characters: the labels are those
; without the percent sign, as above.

(bidi-rule-test-is 5 *bidi-rule-test-terminator-characters* :strict *ltr*
                   *v17* 36543 0)

; The Bidi Rule as it is written, with the zero width non-joiner (BN)
; added to the thirteen characters: among the labels of four characters,
; thirty-six are displayed like another; there are none among
; the shorter ones.

(defconst *bidi-rule-test-neutral-characters*
  (append *bidi-rule-test-strict-characters* '(#x200C)))

(bidi-rule-test-is 3 *bidi-rule-test-neutral-characters* :rule *ltr* *v17*
                   294 0)
(bidi-rule-test-is 4 *bidi-rule-test-neutral-characters* :rule *ltr* *v17*
                   3714 36)
(bidi-rule-test-is 4 *bidi-rule-test-neutral-characters* :rule *rtl* *v17*
                   3714 36)

;;;;;;;;;;;;;;;;;;;;

; Sixteen characters for the wide rule: the thirteen, the percent sign (ET),
; and the less-than and greater-than signs (ON), which are displayed
; as their mirror images at a right-to-left level
; and are not paired brackets.

(defconst *bidi-rule-test-wide-characters*
  (append *bidi-rule-test-strict-characters* '(#x25 #x3C #x3E)))

; The wide rule: no two right-to-left names are displayed alike
; in a paragraph from left to right.
; The same search for six characters, 4,437,669 names
; and none displayed like another,
; was run once, on 2026-11-24, outside the certified books.

(bidi-rule-test-is 1 *bidi-rule-test-wide-characters* :wide *ltr* *v17*
                   3 0)
(bidi-rule-test-is 2 *bidi-rule-test-wide-characters* :wide *ltr* *v17*
                   69 0)
(bidi-rule-test-is 3 *bidi-rule-test-wide-characters* :wide *ltr* *v17*
                   1215 0)
(bidi-rule-test-is 4 *bidi-rule-test-wide-characters* :wide *ltr* *v17*
                   19455 0)
(bidi-rule-test-is 5 *bidi-rule-test-wide-characters* :wide *ltr* *v17*
                   297633 0)

; For 16.0.0 and 18.0.0, up to four characters.

(bidi-rule-test-is 4 *bidi-rule-test-wide-characters* :wide *ltr*
                   (version-v16.0.0) 19455 0)
(bidi-rule-test-is 4 *bidi-rule-test-wide-characters* :wide *ltr*
                   (version-v18.0.0) 19455 0)

; In a paragraph from right to left the wide rule does not do it:
; three of the names of two characters are displayed like another.

(bidi-rule-test-is 2 *bidi-rule-test-wide-characters* :wide *rtl* *v17*
                   69 3)

;;;;;;;;;;;;;;;;;;;;

; Labels of the two kinds together.
; Eleven characters, with letters of class L: a, b (L); alef, bet (R);
; 1, 2 (EN); Arabic-Indic one (AN); hyphen (ES); comma (CS);
; asterisk (ON); sheva (NSM).
; The search compares all the labels that satisfy the strict rule,
; the left-to-right ones and the right-to-left ones:
; none is displayed like another, in a paragraph of either direction.
; The same search for six characters, 85,486 labels
; and none displayed like another in either direction,
; was run once, on 2026-11-24, outside the certified books.

(defconst *bidi-rule-test-mixed-characters*
  '(#x61 #x62 #x5D0 #x5D1 #x31 #x32 #x661 #x2D #x2C #x2A #x5B0))

(bidi-rule-test-is 1 *bidi-rule-test-mixed-characters* :strict-all *ltr*
                   *v17* 4 0)
(bidi-rule-test-is 2 *bidi-rule-test-mixed-characters* :strict-all *ltr*
                   *v17* 22 0)
(bidi-rule-test-is 3 *bidi-rule-test-mixed-characters* :strict-all *ltr*
                   *v17* 168 0)
(bidi-rule-test-is 4 *bidi-rule-test-mixed-characters* :strict-all *ltr*
                   *v17* 1342 0)
(bidi-rule-test-is 5 *bidi-rule-test-mixed-characters* :strict-all *ltr*
                   *v17* 10728 0)

(bidi-rule-test-is 1 *bidi-rule-test-mixed-characters* :strict-all *rtl*
                   *v17* 4 0)
(bidi-rule-test-is 2 *bidi-rule-test-mixed-characters* :strict-all *rtl*
                   *v17* 22 0)
(bidi-rule-test-is 3 *bidi-rule-test-mixed-characters* :strict-all *rtl*
                   *v17* 168 0)
(bidi-rule-test-is 4 *bidi-rule-test-mixed-characters* :strict-all *rtl*
                   *v17* 1342 0)
(bidi-rule-test-is 5 *bidi-rule-test-mixed-characters* :strict-all *rtl*
                   *v17* 10728 0)

; The same for the wide rule, in a paragraph from left to right,
; with the percent sign (ET) added to the eleven characters.
; The same search for six characters, 816,451 names
; and none displayed like another,
; was run once, on 2026-11-24, outside the certified books.

(defconst *bidi-rule-test-mixed-terminator-characters*
  (append *bidi-rule-test-mixed-characters* '(#x25)))

(bidi-rule-test-is 1 *bidi-rule-test-mixed-terminator-characters* :wide-all
                   *ltr* *v17* 11 0)
(bidi-rule-test-is 2 *bidi-rule-test-mixed-terminator-characters* :wide-all
                   *ltr* *v17* 111 0)
(bidi-rule-test-is 3 *bidi-rule-test-mixed-terminator-characters* :wide-all
                   *ltr* *v17* 1063 0)
(bidi-rule-test-is 4 *bidi-rule-test-mixed-terminator-characters* :wide-all
                   *ltr* *v17* 9887 0)
(bidi-rule-test-is 5 *bidi-rule-test-mixed-terminator-characters* :wide-all
                   *ltr* *v17* 90351 0)
