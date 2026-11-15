; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "normalization-test-types")
(include-book "../normalization")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book defines how to run the normalization conformance test of the
; Unicode Character Database, NormalizationTest.txt.  The books
; normalization-test-v<version> in this directory run it, on the test data
; that is in ../data/v<version>/normalization-test.lisp.  The fixtypes of the
; test data are in the book normalization-test-types.
;
; The test file says what a conforming implementation must do:
;
; 1. For each line of the file, with columns c1, c2, c3, c4, c5:
;
;      NFC:   c2 == toNFC(c1) == toNFC(c2) == toNFC(c3)
;             c4 == toNFC(c4) == toNFC(c5)
;      NFD:   c3 == toNFD(c1) == toNFD(c2) == toNFD(c3)
;             c5 == toNFD(c4) == toNFD(c5)
;      NFKC:  c4 == toNFKC(c1) == toNFKC(c2) == toNFKC(c3)
;                == toNFKC(c4) == toNFKC(c5)
;      NFKD:  c5 == toNFKD(c1) == toNFKD(c2) == toNFKD(c3)
;                == toNFKD(c4) == toNFKD(c5)
;
; 2. For every code point X assigned in this version of Unicode
;    that is not specifically listed in Part 1 (as the c1 of a line):
;
;      X == toNFC(X) == toNFD(X) == toNFKC(X) == toNFKD(X)
;
; The columns c1, c2, c3, c4 and c5 are the fields
; source, nfc, nfd, nfkc and nfkd of a line.
;
; We check 1 for all the lines of all the parts.
; We check 2 for all the code points that are not listed in Part 1,
; assigned or not, and including the surrogates:
; this is more than the test asks for.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Requirement 1.

(define normalization-test-line-passes-p ((line normalization-test-line-p)
                                          (ver versionp))
  :returns (yes/no booleanp)
  (b* (((normalization-test-line line)))
    (and
     ;; NFC
     (equal line.nfc (nfc line.source ver))
     (equal line.nfc (nfc line.nfc ver))
     (equal line.nfc (nfc line.nfd ver))
     (equal line.nfkc (nfc line.nfkc ver))
     (equal line.nfkc (nfc line.nfkd ver))
     ;; NFD
     (equal line.nfd (nfd line.source ver))
     (equal line.nfd (nfd line.nfc ver))
     (equal line.nfd (nfd line.nfd ver))
     (equal line.nfkd (nfd line.nfkc ver))
     (equal line.nfkd (nfd line.nfkd ver))
     ;; NFKC
     (equal line.nfkc (nfkc line.source ver))
     (equal line.nfkc (nfkc line.nfc ver))
     (equal line.nfkc (nfkc line.nfd ver))
     (equal line.nfkc (nfkc line.nfkc ver))
     (equal line.nfkc (nfkc line.nfkd ver))
     ;; NFKD
     (equal line.nfkd (nfkd line.source ver))
     (equal line.nfkd (nfkd line.nfc ver))
     (equal line.nfkd (nfkd line.nfd ver))
     (equal line.nfkd (nfkd line.nfkc ver))
     (equal line.nfkd (nfkd line.nfkd ver)))))

; The lines of a list that fail, in order.

(define normalization-test-lines-failures ((lines normalization-test-line-listp)
                                           (ver versionp))
  :returns (failures normalization-test-line-listp
                     :hints (("Goal" :induct t)))
  (cond ((endp lines) nil)
        ((normalization-test-line-passes-p (car lines) ver)
         (normalization-test-lines-failures (cdr lines) ver))
        (t (cons (normalization-test-line-fix (car lines))
                 (normalization-test-lines-failures (cdr lines) ver))))
  :hooks nil)

; The lines of the parts of a test that fail, in order.

(define normalization-test-failures ((parts normalization-test-part-listp)
                                     (ver versionp))
  :returns (failures normalization-test-line-listp
                     :hints (("Goal" :induct t)))
  (cond ((endp parts) nil)
        (t (append (normalization-test-lines-failures
                    (normalization-test-part->lines (car parts))
                    ver)
                   (normalization-test-failures (cdr parts) ver))))
  :hooks nil)

; The number of lines of the parts of a test.

(define normalization-test-line-count ((parts normalization-test-part-listp))
  :returns (count natp
                  :rule-classes (:rewrite :type-prescription)
                  :hints (("Goal" :induct t)))
  (cond ((endp parts) 0)
        (t (+ (len (normalization-test-part->lines (car parts)))
              (normalization-test-line-count (cdr parts)))))
  :hooks nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Requirement 2.

; The lines of the part with a given number; none if there is no such part.

(define normalization-test-part-lines ((number natp)
                                       (parts normalization-test-part-listp))
  :returns (lines normalization-test-line-listp
                  :hints (("Goal" :induct t)))
  (b* (((when (endp parts)) nil)
       ((normalization-test-part part) (car parts))
       ((when (equal part.number (lnfix number))) part.lines))
    (normalization-test-part-lines number (cdr parts)))
  :hooks nil)

; The code points that lines list:
; a line lists a code point if its source consists of that code point.

(define normalization-test-listed ((lines normalization-test-line-listp))
  :returns (cps code-point-listp
                :hints (("Goal" :induct t)))
  (b* (((when (endp lines)) nil)
       ((normalization-test-line line) (car lines))
       (rest (normalization-test-listed (cdr lines))))
    (if (equal (len line.source) 1)
        (cons (code-point-fix (first line.source)) rest)
      rest))
  :hooks nil)

; Check if no normalization form changes a code point.

(define normalization-unchanged-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  (b* ((cps (list (code-point-fix cp))))
    (and (equal cps (nfc cps ver))
         (equal cps (nfd cps ver))
         (equal cps (nfkc cps ver))
         (equal cps (nfkd cps ver)))))

; Add to CHANGED the code points of a list that some normalization form
; changes.  The list may be long, so this is tail recursive.

(define normalization-changed-code-points ((cps code-point-listp)
                                           (ver versionp)
                                           (changed code-point-listp))
  :returns (new-changed code-point-listp
                        :hints (("Goal" :induct t)))
  (b* (((when (endp cps)) (code-point-list-fix changed))
       (cp (code-point-fix (car cps))))
    (normalization-changed-code-points
     (cdr cps)
     ver
     (if (normalization-unchanged-p cp ver)
         changed
       (cons cp changed))))
  :hooks nil)

; The code points that fail:
; those that some normalization form changes and that Part 1 does not list.

(define normalization-test-unlisted-failures
  ((parts normalization-test-part-listp) (ver versionp))
  :returns (failures code-point-listp)
  (set-difference-equal
   (normalization-changed-code-points (all-code-points) ver nil)
   (normalization-test-listed (normalization-test-part-lines 1 parts)))
  :hooks nil)
