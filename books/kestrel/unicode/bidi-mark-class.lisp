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
(include-book "bidi-rule")

(local (include-book "range-operations"))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection bidi-combining-mark-class
  :parents (bidi-rule-display)
  :short "A code point whose class is not @('L') (@('Left_To_Right'))
          is a combining mark exactly when its class is @('NSM')
          (@('Nonspacing_Mark'))."
  :long
  (xdoc::topstring
   (xdoc::p
    "Rule L3 of the Unicode Bidirectional Algorithm
     goes by the general category of a character
     (see @(tsee bidi-combining-mark-p)),
     and rule W1 by its bidirectional class
     (see @(tsee bidi-mark-code-point-p)).
     Some combining marks have the class @('L');
     apart from those, the two predicates agree.
     We prove it by computing with lists of ranges of code points,
     for each version:
     the code points for which exactly one of the two predicates holds,
     less the code points of class @('L'),
     are a list of ranges, and that list is empty.
     So adding a version checks it for that version."))

  ;; The code points of the three general categories of combining marks,
  ;; as a list of ranges.

  (local
   (define mark-ranges ((ver versionp))
     :returns (ranges range-listp)
     (ranges-union
      (general-category-ranges (general-category-nonspacing-mark) ver)
      (ranges-union
       (general-category-ranges (general-category-spacing-mark) ver)
       (general-category-ranges (general-category-enclosing-mark) ver)))
     :hooks nil))

  (defrulel code-point-in-mark-ranges
    (equal (code-point-in-ranges-p cp (mark-ranges ver))
           (bidi-combining-mark-p cp ver))
    :enable (mark-ranges
             bidi-combining-mark-p
             general-category-mark-p
             code-point-in-general-category-ranges
             equal-of-general-category-nonspacing-mark
             equal-of-general-category-spacing-mark
             equal-of-general-category-enclosing-mark)
    :disable ((:e general-category-nonspacing-mark)
              (:e general-category-spacing-mark)
              (:e general-category-enclosing-mark)))

  ;; The code points of the two classes, as lists of ranges.

  (defrulel code-point-in-ranges-of-class-nonspacing-mark
    (equal (code-point-in-ranges-p
            cp
            (bidi-class-ranges (bidi-class-nonspacing-mark) ver))
           (bidi-mark-code-point-p cp ver))
    :enable (bidi-mark-code-point-p
             code-point-in-bidi-class-ranges
             equal-of-bidi-class-nonspacing-mark)
    :disable ((:e bidi-class-nonspacing-mark)))

  (defrulel code-point-in-ranges-of-class-left-to-right
    (equal (code-point-in-ranges-p
            cp
            (bidi-class-ranges (bidi-class-left-to-right) ver))
           (equal (bidi-class-kind (code-point-bidi-class cp ver))
                  :left-to-right))
    :enable (code-point-in-bidi-class-ranges
             equal-of-bidi-class-left-to-right)
    :disable ((:e bidi-class-left-to-right)))

  ;; The code points for which exactly one of the two predicates holds,
  ;; less the code points of class L, as a list of ranges.

  (local
   (define mark-class-exceptions ((ver versionp))
     :returns (ranges range-listp)
     (b* ((marks (mark-ranges ver))
          (class-marks (bidi-class-ranges (bidi-class-nonspacing-mark) ver))
          (left-to-right (bidi-class-ranges (bidi-class-left-to-right) ver)))
       (ranges-difference
        (ranges-union (ranges-difference marks class-marks)
                      (ranges-difference class-marks marks))
        left-to-right))
     :hooks nil))

  (defruledl code-point-in-mark-class-exceptions
    (equal (code-point-in-ranges-p cp (mark-class-exceptions ver))
           (and (not (equal (bidi-combining-mark-p cp ver)
                            (bidi-mark-code-point-p cp ver)))
                (not (equal (bidi-class-kind (code-point-bidi-class cp ver))
                            :left-to-right))))
    :enable mark-class-exceptions
    :disable ((:e bidi-class-nonspacing-mark)
              (:e bidi-class-left-to-right)))

  ;; There are none: this is checked by evaluation, for each version.

  (defrulel no-mark-class-exceptions
    (equal (mark-class-exceptions (version-fix ver))
           nil)
    :enable version-fix-in-terms-of-version-case)

  (defruled bidi-combining-mark-p-when-not-left-to-right
    (implies (not (equal (bidi-class-kind (code-point-bidi-class cp ver))
                         :left-to-right))
             (equal (bidi-combining-mark-p cp ver)
                    (bidi-mark-code-point-p cp ver)))
    :use (:instance code-point-in-mark-class-exceptions
                    (ver (version-fix ver)))))
