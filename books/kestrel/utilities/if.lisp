; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Some simple rewrite rules about IF.  These may be needed by Axe if not by
;; ACL2.  I suppose some might help during backchaining, but most of this
;; knowledge may be built into ACL2, and the ACL2 rewriter usually handles IF
;; by splitting a proof into cases.

(defthmd if-same-branches
  (equal (if test x x)
         x))

(defthmd if-of-t
  (equal (if t thenpart elsepart)
         thenpart))

(defthmd if-when-non-nil-constant
  (implies (and (syntaxp (quotep test))
                test)
           (equal (if test thenpart elsepart)
                  thenpart)))

(defthmd if-of-nil
  (equal (if nil thenpart elsepart)
         elsepart))

(defthmd if-of-not
  (equal (if (not test) x y)
         (if test y x)))

(defthmd if-nil-t
  (equal (if test nil t)
         (not test)))

;; When rewriting an IF in an IFF context (e.g., when it appears in the test of
;; another IF), replace (if test t nil) with just the test.  This was needed
;; for a call of the SIMPLIFY tool.
(defthm if-of-t-and-nil-under-iff
  (iff (if test t nil)
       test))

(defthmd if-of-t-and-nil-when-booleanp
  (implies (booleanp x)
           (equal (if x t nil)
                  x)))

(defthmd equal-of-if-arg1
  (equal (equal (if test x y) z)
         (if test
             (equal x z)
           (equal y z))))

(defthmd equal-of-if-arg2
  (equal (equal z (if test x y))
         (if test
             (equal z x)
           (equal z y))))

;; Safer, since the term that is getting replicated in the RHS (z) is a constant.
(defthmd equal-of-if-arg1-when-quotep
  (implies (syntaxp (quotep z))
           (equal (equal (if test x y) z)
                  (if test
                      (equal x z)
                    (equal y z)))))

;; Safer, since the term that is getting replicated in the RHS (z) is a constant.
(defthmd equal-of-if-arg2-when-quotep
  (implies (syntaxp (quotep z))
           (equal (equal z (if test x y))
                  (if test
                      (equal z x)
                    (equal z y)))))

;; Enable, for backchaining?  Will it even fire?
(defthmd not-of-if
  (equal (not (if test tp ep))
         (if test (not tp) (not ep))))
