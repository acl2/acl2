; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../normalization")

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book defines how to run the normalization conformance test of the
; Unicode Character Database, NormalizationTest.txt.  The books
; normalization-test-v<version> in this directory run it, on the test data
; that is in ../data/v<version>/normalization-test.lisp.
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
; We check 1 for all the lines of all the parts.
; We check 2 for all the code points that are not listed in Part 1,
; assigned or not, and including the surrogates:
; this is more than the test asks for.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The test data: a list of parts, each a number followed by lines,
; each line a list of five lists of code points.

(define normalization-test-line-p (x)
  :returns (yes/no booleanp)
  (and (true-listp x)
       (equal (len x) 5)
       (code-point-listp (first x))
       (code-point-listp (second x))
       (code-point-listp (third x))
       (code-point-listp (fourth x))
       (code-point-listp (fifth x))))

(define normalization-test-line-listp (x)
  :returns (yes/no booleanp)
  (cond ((atom x) (null x))
        (t (and (normalization-test-line-p (car x))
                (normalization-test-line-listp (cdr x))))))

(define normalization-test-p (x)
  :returns (yes/no booleanp)
  (cond ((atom x) (null x))
        (t (and (consp (car x))
                (natp (car (car x)))
                (normalization-test-line-listp (cdr (car x)))
                (normalization-test-p (cdr x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Requirement 1.

(define normalization-test-line-passes-p ((line normalization-test-line-p)
                                          (ver versionp))
  :returns (yes/no booleanp)
  (b* ((c1 (first line))
       (c2 (second line))
       (c3 (third line))
       (c4 (fourth line))
       (c5 (fifth line)))
    (and
     ;; NFC
     (equal c2 (nfc c1 ver))
     (equal c2 (nfc c2 ver))
     (equal c2 (nfc c3 ver))
     (equal c4 (nfc c4 ver))
     (equal c4 (nfc c5 ver))
     ;; NFD
     (equal c3 (nfd c1 ver))
     (equal c3 (nfd c2 ver))
     (equal c3 (nfd c3 ver))
     (equal c5 (nfd c4 ver))
     (equal c5 (nfd c5 ver))
     ;; NFKC
     (equal c4 (nfkc c1 ver))
     (equal c4 (nfkc c2 ver))
     (equal c4 (nfkc c3 ver))
     (equal c4 (nfkc c4 ver))
     (equal c4 (nfkc c5 ver))
     ;; NFKD
     (equal c5 (nfkd c1 ver))
     (equal c5 (nfkd c2 ver))
     (equal c5 (nfkd c3 ver))
     (equal c5 (nfkd c4 ver))
     (equal c5 (nfkd c5 ver))))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable normalization-test-line-p))))

; The lines that fail, most recent first.

(define normalization-test-lines-failures ((lines normalization-test-line-listp)
                                           (ver versionp)
                                           (failures true-listp))
  :returns (new-failures true-listp :hyp (true-listp failures))
  (cond ((endp lines) failures)
        (t (normalization-test-lines-failures
            (cdr lines)
            ver
            (if (normalization-test-line-passes-p (car lines) ver)
                failures
              (cons (car lines) failures)))))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable normalization-test-line-listp))))

(define normalization-test-failures ((test normalization-test-p)
                                     (ver versionp)
                                     (failures true-listp))
  :returns (new-failures true-listp :hyp (true-listp failures))
  (cond ((endp test) failures)
        (t (normalization-test-failures
            (cdr test)
            ver
            (normalization-test-lines-failures (cdr (car test))
                                               ver
                                               failures))))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable normalization-test-p))))

(define normalization-test-count ((test normalization-test-p))
  :returns (count natp)
  (cond ((endp test) 0)
        (t (+ (len (cdr (car test)))
              (normalization-test-count (cdr test)))))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable normalization-test-p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Requirement 2.

; The code points listed in Part 1, i.e. the first columns of its lines.
; Each consists of one code point, and they are in increasing order;
; the function returns :bad if that is not so.

(define normalization-test-listed ((lines normalization-test-line-listp)
                                   (previous integerp))
  :returns (listed (or (nat-listp listed)
                       (equal listed :bad)))
  (b* (((when (endp lines)) nil)
       (c1 (first (car lines)))
       ((unless (and (consp c1)
                     (endp (cdr c1))
                     (natp (car c1))
                     (< previous (car c1))))
        :bad)
       (rest (normalization-test-listed (cdr lines) (car c1)))
       ((when (equal rest :bad)) :bad))
    (cons (car c1) rest))
  :hooks nil
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (enable normalization-test-line-listp
                                           normalization-test-line-p
                                           code-point-p))))

; Check a code point that is not listed.

(define unlisted-code-point-passes-p ((cp code-point-p) (ver versionp))
  :returns (yes/no booleanp)
  (b* ((cps (list cp)))
    (and (equal cps (nfc cps ver))
         (equal cps (nfd cps ver))
         (equal cps (nfkc cps ver))
         (equal cps (nfkd cps ver))))
  :hooks nil)

; Go through all the code points from CP on, skipping the listed ones
; (LISTED has the listed code points that are not below CP, in order).
; Return the code points that fail, most recent first.

(define unlisted-code-points-failures ((cp natp)
                                       (listed nat-listp)
                                       (ver versionp)
                                       (failures true-listp))
  :returns (new-failures true-listp :hyp (true-listp failures))
  (b* (((unless (mbt (natp cp))) failures)
       ((when (> cp #x10FFFF)) failures)
       ((when (and (consp listed)
                   (equal (car listed) cp)))
        (unlisted-code-points-failures (+ 1 cp) (cdr listed) ver failures)))
    (unlisted-code-points-failures
     (+ 1 cp)
     listed
     ver
     (if (unlisted-code-point-passes-p cp ver)
         failures
       (cons cp failures))))
  :measure (nfix (- #x110000 (nfix cp)))
  :hooks nil
  :guard-hints (("Goal" :in-theory (enable code-point-p nat-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The whole test.  The result is a list of three things, which is
; (NIL NIL <the number of lines>) if and only if the test passes:
; the lines that fail requirement 1;
; the code points that fail requirement 2
; (or :BAD if Part 1 is not as expected);
; and the number of lines, so that an empty test does not pass unnoticed.

(define run-normalization-test ((test normalization-test-p) (ver versionp))
  :returns (result true-listp)
  (b* ((part1 (assoc 1 test))
       (listed (if (consp part1)
                   (normalization-test-listed (cdr part1) -1)
                 :bad)))
    (list (normalization-test-failures test ver nil)
          (if (equal listed :bad)
              :bad
            (unlisted-code-points-failures 0 listed ver nil))
          (normalization-test-count test)))
  :hooks nil
  :guard-hints (("Goal"
                 :use (:instance return-type-of-normalization-test-listed
                                 (lines (cdr (assoc-equal 1 test)))
                                 (previous -1))))
  :prepwork
  ((defrulel alistp-when-normalization-test-p
     (implies (normalization-test-p x)
              (alistp x))
     :induct t
     :enable (normalization-test-p alistp))
   (defrulel normalization-test-line-listp-of-cdr-of-assoc
     (implies (normalization-test-p x)
              (normalization-test-line-listp (cdr (assoc-equal n x))))
     :induct t
     :enable (normalization-test-p
              normalization-test-line-listp
              assoc-equal))))
