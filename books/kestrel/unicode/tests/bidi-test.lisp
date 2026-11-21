; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The conformance test of the Unicode Bidirectional Algorithm
; on bidirectional classes, BidiTest.txt:
; every line of the file, in every paragraph direction that it asks for.
; The file is the same for the three supported versions of Unicode,
; and it has no code points, so the test is run once.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-test-types")
(include-book "../bidi-reordering")
(include-book "../data/bidi/bidi-test")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp character-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The class that a character of the test data stands for.

(define bidi-test-class ((char characterp))
  :returns (class bidi-class-p)
  (case char
    (#\L (bidi-class-left-to-right))
    (#\R (bidi-class-right-to-left))
    (#\A (bidi-class-arabic-letter))
    (#\E (bidi-class-european-number))
    (#\s (bidi-class-european-separator))
    (#\t (bidi-class-european-terminator))
    (#\N (bidi-class-arabic-number))
    (#\c (bidi-class-common-separator))
    (#\M (bidi-class-nonspacing-mark))
    (#\b (bidi-class-boundary-neutral))
    (#\B (bidi-class-paragraph-separator))
    (#\S (bidi-class-segment-separator))
    (#\W (bidi-class-white-space))
    (#\O (bidi-class-other-neutral))
    (#\e (bidi-class-left-to-right-embedding))
    (#\o (bidi-class-left-to-right-override))
    (#\f (bidi-class-right-to-left-embedding))
    (#\p (bidi-class-right-to-left-override))
    (#\d (bidi-class-pop-directional-format))
    (#\i (bidi-class-left-to-right-isolate))
    (#\j (bidi-class-right-to-left-isolate))
    (#\k (bidi-class-first-strong-isolate))
    (otherwise (bidi-class-pop-directional-isolate))) ; #\q
  :hooks nil)

; The characters of the strings of a group, one string after the other.

(define bidi-test-input-chars ((inputs bidi-test-input-listp))
  :returns (chars character-listp :hints (("Goal" :induct t)))
  (if (endp inputs)
      nil
    (append (coerce (acl2::str-fix (car inputs)) 'list)
            (bidi-test-input-chars (cdr inputs))))
  :hooks nil)

; The classes of the next input, which has N characters,
; and the characters after it.

(define bidi-test-take-classes ((n natp) (chars character-listp))
  :returns (mv (classes bidi-class-listp :hints (("Goal" :induct t)))
               (rest character-listp
                     :hyp (character-listp chars)
                     :hints (("Goal" :induct t))))
  (b* (((when (or (zp n)
                  (endp chars)))
        (mv nil chars))
       ((mv classes rest) (bidi-test-take-classes (- n 1) (cdr chars))))
    (mv (cons (bidi-test-class (car chars)) classes)
        rest))
  :hooks nil)

; Check one input in one paragraph direction.

(define bidi-test-passes-p ((classes bidi-class-listp)
                            (paragraph-level natp)
                            (levels bidi-level-option-listp)
                            (order nat-listp))
  :returns (yes/no booleanp)
  (b* ((got (bidi-paragraph-levels (bidi-classes-to-chars classes)
                                   paragraph-level)))
    (and (equal got levels)
         (equal (bidi-order-of-levels got) order)))
  :hooks nil)

; The number of the paragraph directions of a group
; in which an input fails.  The directions are given as in the file:
; 1 for the direction that rules P2 and P3 find,
; 2 for left to right, 4 for right to left, added up.

(define bidi-test-input-failures ((classes bidi-class-listp)
                                  (group bidi-test-group-p))
  :returns (count natp :rule-classes (:rewrite :type-prescription))
  (b* (((bidi-test-group group)))
    (+ (if (and (logbitp 0 group.directions)
                (not (bidi-test-passes-p
                      classes
                      (bidi-first-strong-level classes nil)
                      group.levels
                      group.order)))
           1
         0)
       (if (and (logbitp 1 group.directions)
                (not (bidi-test-passes-p classes 0 group.levels group.order)))
           1
         0)
       (if (and (logbitp 2 group.directions)
                (not (bidi-test-passes-p classes 1 group.levels group.order)))
           1
         0)))
  :hooks nil)

; The number of failures among the next COUNT inputs of a group, added to
; FAILURES.

(define bidi-test-inputs-failures ((count natp)
                                   (chars character-listp)
                                   (group bidi-test-group-p)
                                   (failures natp))
  :returns (new-failures natp :rule-classes (:rewrite :type-prescription)
                         :hints (("Goal" :induct t)))
  (b* (((when (zp count)) (lnfix failures))
       ((mv classes rest)
        (bidi-test-take-classes (len (bidi-test-group->levels group))
                                chars)))
    (bidi-test-inputs-failures
     (- count 1)
     rest
     group
     (+ (lnfix failures)
        (bidi-test-input-failures classes group))))
  :hooks nil)

; The number of inputs of a group.

(define bidi-test-group-input-count ((group bidi-test-group-p))
  :returns (count natp :rule-classes (:rewrite :type-prescription))
  (b* (((bidi-test-group group))
       (length (len group.levels))
       ((when (equal length 0)) 0))
    (nfix (floor (len (bidi-test-input-chars group.inputs)) length)))
  :hooks nil)

; The number of failures of a list of groups, added to FAILURES.

(define bidi-test-failures ((groups bidi-test-group-listp)
                            (failures natp))
  :returns (new-failures natp :rule-classes (:rewrite :type-prescription)
                         :hints (("Goal" :induct t)))
  (b* (((when (endp groups)) (lnfix failures))
       (group (car groups)))
    (bidi-test-failures
     (cdr groups)
     (bidi-test-inputs-failures
      (bidi-test-group-input-count group)
      (bidi-test-input-chars (bidi-test-group->inputs group))
      group
      failures)))
  :hooks nil)

; The number of lines of the file in a list of groups, added to LINES,
; and the number of tests, counting each direction of each line,
; added to TESTS.

(define bidi-test-counts ((groups bidi-test-group-listp)
                          (lines natp)
                          (tests natp))
  :returns (mv (new-lines natp :rule-classes (:rewrite :type-prescription)
                          :hints (("Goal" :induct t)))
               (new-tests natp :rule-classes (:rewrite :type-prescription)
                          :hints (("Goal" :induct t))))
  (b* (((when (endp groups)) (mv (lnfix lines) (lnfix tests)))
       (group (car groups))
       (count (bidi-test-group-input-count group)))
    (bidi-test-counts
     (cdr groups)
     (+ (lnfix lines) count)
     (+ (lnfix tests)
        (* count (logcount (bidi-test-group->directions group))))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The file has 490,846 lines, which are 770,241 tests.

(assert-event
 (mv-let (lines tests)
     (bidi-test-counts *bidi-test* 0 0)
   (and (equal lines 490846)
        (equal tests 770241))))

; No test fails.

(assert-event (equal (bidi-test-failures *bidi-test* 0) 0))
