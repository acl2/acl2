; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
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

;; See also ../booleans/bool-fix.lisp.

(defthmd if-same-branches
  (equal (if test x x)
         x))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Are these ever needed?

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd if-of-not
  (equal (if (not test) x y)
         (if test y x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;See also if-of-t-and-nil-becomes-bool-fix
(defthmd if-of-t-and-nil-when-booleanp
  (implies (booleanp test)
           (equal (if test t nil)
                  test)))

;rename
(defthmd if-nil-t
  (equal (if test nil t)
         (not test)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename if-same-arg2-when-booleanp
(defthm if-x-x-y-when-booleanp
  (implies (and (syntaxp (not (quotep test))) ; avoid loops
                (booleanp test))
           (equal (if test test else)
                  (if test t else))))

;rename if-same-arg3
(defthm if-x-y-x
  (equal (if test then test)
         (if test then nil)))

(defthmd if-of-not-same-arg2
  (equal (if test (not test) else)
         (if test nil else)))

(defthm if-of-not-same-arg3
  (equal (if test then (not test))
         (if test then t)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; When rewriting an IF in an IFF context (e.g., when it appears in the test of
;; another IF), replace (if test t nil) with just the test.  This was needed
;; for a call of the SIMPLIFY tool.
(defthm if-of-t-and-nil-under-iff
  (iff (if test t nil)
       test))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; (defthm equal-of-constant-and-if
;;   (implies (syntaxp (quotep k))
;;            (equal (equal k (if x y z))
;;                   (if x (equal k y) (equal k z)))))

;; (defthm equal-of-if-and-constant
;;   (implies (syntaxp (quotep k))
;;            (equal (equal (if x y z) k)
;;                   (if x (equal y k) (equal z k)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Enable, for backchaining?  Will it even fire?
(defthmd not-of-if
  (equal (not (if test tp ep))
         (if test (not tp) (not ep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthmd if-of-equal-and-t-and-not-equal-diff
  (implies (not (equal v1 v2))
           (equal (if (equal v1 x) t (not (equal v2 x)))
                  (not (equal v2 x)))))

(defthmd if-of-equal-and-nil-and-equal-diff
  (implies (not (equal v1 v2))
           (equal (if (equal v1 x) nil (equal v2 x))
                  (equal v2 x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;gen the cons?
(defthmd if-of-if-of-cons-arg1-arg2
  (equal (if (if x (cons a b) y) z w)
         (if (if x t y) z w)))

;gen the cons?
(defthmd if-of-if-of-cons-arg1-arg3
  (equal (if (if x y (cons a b)) z w)
         (if (if x y t) z w)))

;; drop since we turn the cons into t and then apply the t-nil rule
;; ;move
;; ;can help when the inner if returns an error (a cons) or nil
;; (defthmd if-of-if-of-cons-and-nil
;;   (equal (if (if test (cons a b) nil) tp ep)
;;          (if test tp ep)))

(defthmd if-of-if-same-arg2
  (equal (if test (if test tp ep) ep2)
         (if test tp ep2)))

(defthmd if-of-if-same-arg3
  (equal (if test x (if test y z))
         (if test x z)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename?
(defthmd if-thm
  (equal (if (if test test t) then else)
         then))

;or go via bool-fix
(defthmd if-of-if-t-nil
  (equal (if (if test t nil) foo bar)
         (if test foo bar)))
