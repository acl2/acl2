; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
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
         thenpart)
  :hints (("Goal" :in-theory (enable if))))

(defthmd if-when-non-nil-constant
  (implies (and (syntaxp (quotep test))
                test)
           (equal (if test thenpart elsepart)
                  thenpart))
  :hints (("Goal" :in-theory (enable if))))

(defthmd if-of-nil
  (equal (if nil thenpart elsepart)
         elsepart)
  :hints (("Goal" :in-theory (enable if))))

(defthmd if-of-not
  (equal (if (not test) x y)
         (if test y x))
  :hints (("Goal" :in-theory (enable if))))

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

(defthmd equal-of-if-arg2
  (equal (equal k (if test x y))
         (if test
             (equal k x)
           (equal k y))))
