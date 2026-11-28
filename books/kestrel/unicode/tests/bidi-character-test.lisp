; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The conformance test of the Unicode Bidirectional Algorithm
; on characters, BidiCharacterTest.txt: every line of the file,
; for each supported version of Unicode.
; The file is the same for the three versions,
; but the properties of its code points are looked up in each version.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "bidi-test-types")
(include-book "../bidi-reordering")
(include-book "../data/bidi/bidi-character-test")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems
(local (include-book "arithmetic/top" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp character-listp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The code point that a character of the test data stands for:
; the code point at the place that the character has
; in the list of characters.

(define bidi-character-test-code-point ((char characterp)
                                        (chars character-listp)
                                        (cps code-point-listp))
  :returns (cp code-point-p :hints (("Goal" :induct t)))
  (cond ((or (endp chars)
             (endp cps))
         0)
        ((eql char (car chars)) (code-point-fix (car cps)))
        (t (bidi-character-test-code-point char (cdr chars) (cdr cps))))
  :hooks nil)

; The characters of the strings of a group, one string after the other.

(define bidi-character-test-input-chars ((inputs bidi-test-input-listp))
  :returns (chars character-listp :hints (("Goal" :induct t)))
  (if (endp inputs)
      nil
    (append (coerce (acl2::str-fix (car inputs)) 'list)
            (bidi-character-test-input-chars (cdr inputs))))
  :hooks nil)

; The code points of the next input, which has N characters,
; and the characters after it.

(define bidi-character-test-take ((n natp) (chars character-listp))
  :returns (mv (cps code-point-listp :hints (("Goal" :induct t)))
               (rest character-listp
                     :hyp (character-listp chars)
                     :hints (("Goal" :induct t))))
  (b* (((when (or (zp n)
                  (endp chars)))
        (mv nil chars))
       ((mv cps rest) (bidi-character-test-take (- n 1) (cdr chars))))
    (mv (cons (bidi-character-test-code-point
               (car chars)
               (coerce *bidi-character-test-characters* 'list)
               *bidi-character-test-code-points*)
              cps)
        rest))
  :hooks nil)

; Check one input: the paragraph embedding level,
; the levels and the order of display.
; The direction of the paragraph is given as in the file:
; 0 for left to right, 1 for right to left,
; 2 for the direction that rules P2 and P3 find.

(define bidi-character-test-passes-p ((cps code-point-listp)
                                      (group bidi-character-test-group-p)
                                      (ver versionp))
  :returns (yes/no booleanp)
  (b* (((bidi-character-test-group group))
       (direction (case group.direction
                    (0 (paragraph-direction-left-to-right))
                    (1 (paragraph-direction-right-to-left))
                    (otherwise (paragraph-direction-first-strong)))))
    (and (equal (bidi-paragraph-embedding-level
                 (code-points-to-bidi-chars cps ver)
                 direction)
                group.paragraph-level)
         (equal (bidi-levels cps direction ver) group.levels)
         (equal (bidi-display-order cps direction ver) group.order)))
  :hooks nil)

; The number of failures among the next COUNT inputs of a group,
; added to FAILURES.

(define bidi-character-test-inputs-failures
  ((count natp)
   (chars character-listp)
   (group bidi-character-test-group-p)
   (ver versionp)
   (failures natp))
  :returns (new-failures natp :rule-classes (:rewrite :type-prescription)
                         :hints (("Goal" :induct t)))
  (b* (((when (zp count)) (lnfix failures))
       ((mv cps rest)
        (bidi-character-test-take
         (len (bidi-character-test-group->levels group))
         chars)))
    (bidi-character-test-inputs-failures
     (- count 1)
     rest
     group
     ver
     (if (bidi-character-test-passes-p cps group ver)
         (lnfix failures)
       (+ 1 (lnfix failures)))))
  :hooks nil)

; The number of inputs of a group.

(define bidi-character-test-group-input-count
  ((group bidi-character-test-group-p))
  :returns (count natp :rule-classes (:rewrite :type-prescription))
  (b* (((bidi-character-test-group group))
       (length (len group.levels))
       ((when (equal length 0)) 0))
    (nfix (floor (len (bidi-character-test-input-chars group.inputs))
                 length)))
  :hooks nil)

; The number of failures of a list of groups, added to FAILURES.

(define bidi-character-test-failures
  ((groups bidi-character-test-group-listp)
   (ver versionp)
   (failures natp))
  :returns (new-failures natp :rule-classes (:rewrite :type-prescription)
                         :hints (("Goal" :induct t)))
  (b* (((when (endp groups)) (lnfix failures))
       (group (car groups)))
    (bidi-character-test-failures
     (cdr groups)
     ver
     (bidi-character-test-inputs-failures
      (bidi-character-test-group-input-count group)
      (bidi-character-test-input-chars
       (bidi-character-test-group->inputs group))
      group
      ver
      failures)))
  :hooks nil)

; The number of lines of the file in a list of groups, added to LINES.

(define bidi-character-test-count
  ((groups bidi-character-test-group-listp)
   (lines natp))
  :returns (new-lines natp :rule-classes (:rewrite :type-prescription)
                      :hints (("Goal" :induct t)))
  (if (endp groups)
      (lnfix lines)
    (bidi-character-test-count
     (cdr groups)
     (+ (lnfix lines)
        (bidi-character-test-group-input-count (car groups)))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; There is a character for each code point.

(assert-event
 (equal (length *bidi-character-test-characters*)
        (len *bidi-character-test-code-points*)))

; The file has 91,707 lines.

(assert-event
 (equal (bidi-character-test-count *bidi-character-test* 0) 91707))

; No line fails, in any of the three versions.

(assert-event
 (equal (bidi-character-test-failures *bidi-character-test*
                                      (version-v16.0.0)
                                      0)
        0))

(assert-event
 (equal (bidi-character-test-failures *bidi-character-test*
                                      (version-v17.0.0)
                                      0)
        0))

(assert-event
 (equal (bidi-character-test-failures *bidi-character-test*
                                      (version-v18.0.0)
                                      0)
        0))
