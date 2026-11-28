; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../bidi-display")

(include-book "std/io/read-file-objects" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book defines a function that compares the text as it is displayed
; (the function bidi-display of this library)
; with what another implementation of the Unicode Bidirectional Algorithm
; gives, on test cases that are read from a file.
; The script icu-display.py, in this directory, writes such a file
; with the ICU library: see the section "Validation" of ../README.md.
;
; The file has one object, a list of cases, each of the form
;
;   (direction code-points displayed levels)
;
; where direction is :ltr, :rtl or :fs (the direction of the paragraph:
; left to right, right to left, or that of the first strong character),
; code-points is the text, a single paragraph,
; displayed is the text as the other implementation displays it,
; with rules L3 and L4 applied and with every character kept,
; and levels is the list of the levels that it gives to the characters.
;
; Each case is counted in one of four groups:
;
;   same      bidi-display gives the same list.
;   levels    It does not, and the other implementation
;             does not give the levels that this library gives
;             to the characters that have a level,
;             which are the levels of the conformance files.
;   placed    It does not, the levels are the same,
;             and it gives the same list when each character that rule X9
;             removes takes the level of the character after it,
;             not of the character before it.
;             (The place of those characters is not specified.
;             This library follows UAX #9, Section 5.2;
;             ICU takes the level of the character after.)
;   other     None of the above.  These are printed, up to ten of them.

(program)

(defun compare-display-direction (keyword)
  (case keyword
    (:ltr (paragraph-direction-left-to-right))
    (:rtl (paragraph-direction-right-to-left))
    (otherwise (paragraph-direction-first-strong))))

; Check that the levels of this library, for the characters that have one,
; are those of a list of levels.

(defun compare-display-levels-agree (levels others)
  (cond ((endp levels) t)
        ((and (car levels)
              (not (equal (car levels) (car others))))
         nil)
        (t (compare-display-levels-agree (cdr levels) (cdr others)))))

; Give each character without a level the level of the character after it,
; or the paragraph embedding level if it is the last one.

(defun compare-display-fill-back (levels paragraph-level)
  (if (endp levels)
      nil
    (let ((rest (compare-display-fill-back (cdr levels) paragraph-level)))
      (cons (or (car levels)
                (if (consp rest) (car rest) paragraph-level))
            rest))))

; The same as bidi-display-paragraph, with the levels filled in that way.

(defun compare-display-other-way (cps direction ver)
  (b* ((chars (code-points-to-bidi-chars cps ver))
       (paragraph-level (bidi-paragraph-embedding-level chars direction))
       (levels (compare-display-fill-back
                (bidi-paragraph-levels chars paragraph-level)
                paragraph-level))
       ((mv levels &)
        (bidi-reset-all-levels (bidi-char-list-classes chars)
                               levels
                               paragraph-level))
       (order (bidi-order-of-levels levels))
       (shown (bidi-shown-chars-at order (bidi-shown-chars cps levels))))
    (bidi-mirror-chars (bidi-move-marks shown nil ver) ver)))

(defun compare-display-cases (cases ver same levels placed other)
  (b* (((when (endp cases))
        (prog2$ (cw "compare-display: ~x0 cases: same ~x1, levels ~x2, ~
                     placed ~x3, other ~x4~%"
                    (+ same levels placed other)
                    same levels placed other)
                (equal other 0)))
       (case (car cases))
       (direction (compare-display-direction (first case)))
       (cps (second case))
       (displayed (third case))
       ((when (equal (bidi-display cps direction ver) displayed))
        (compare-display-cases (cdr cases) ver (+ 1 same) levels placed
                               other))
       ((unless (compare-display-levels-agree
                 (bidi-levels cps direction ver)
                 (fourth case)))
        (compare-display-cases (cdr cases) ver same (+ 1 levels) placed
                               other))
       ((when (equal (compare-display-other-way cps direction ver)
                     displayed))
        (compare-display-cases (cdr cases) ver same levels (+ 1 placed)
                               other))
       (- (and (< other 10)
               (cw "compare-display: ~x0 ~x1~%  there ~x2~%  here  ~x3~%"
                   (first case)
                   cps
                   displayed
                   (bidi-display cps direction ver)))))
    (compare-display-cases (cdr cases) ver same levels placed (+ 1 other))))

; Compare.  For example:
;   (compare-display (version-v16.0.0) "/tmp/icu-cases.lsp" state)
; The result is T if no case is in the group `other'.

(defun compare-display (ver filename state)
  (declare (xargs :stobjs state))
  (b* (((mv objects state) (acl2::read-file-objects filename state))
       ((unless (and (consp objects)
                     (true-listp (car objects))))
        (prog2$ (er hard? 'compare-display "Cannot read ~x0." filename)
                (mv nil state))))
    (mv (compare-display-cases (car objects) ver 0 0 0 0)
        state)))
