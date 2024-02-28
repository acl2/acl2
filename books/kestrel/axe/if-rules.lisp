; Rules about IF
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/booleans/bool-fix-def" :dir :system)

;; These rules are for Axe, not ACL2, since ACL2 will split on IFs automatically.

;; TODO: Standardize param names in these.

(defthmd booleanp-of-iff
  (booleanp (iff x y)))

;to be used as an inside-out rule; we need the hyp!
(defthm if-when-not-nil
  (implies test
           (equal (if test x y)
                  x))
  :rule-classes nil)

;to be used as an inside-out rule; we need the hyp!
(defthm if-when-nil
  (implies (not test)
           (equal (if test x y)
                  y))
  :rule-classes nil)

;; ;drop?
;; (defthm if-of-non-nil
;;   (implies (not (equal test nil))
;;            (equal (if test b c)
;;                   b))
;;   :rule-classes nil)

;rename?
(defthmd if-thm
  (equal (if (if x x t) y z)
         y))

(defthmd if-of-t-and-nil-becomes-bool-fix
  (equal (if test t nil)
         (bool-fix test))
  :hints (("Goal" :in-theory (enable bool-fix$inline))))

(defthmd if-of-bool-fix
  (equal (if (bool-fix test) x y)
         (if test x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline))))

;or go via bool-fix, and prove if-of-bool-fix
(defthmd if-of-if-t-nil
  (equal (if (if test t nil) foo bar)
         (if test foo bar)))

(defthm if-x-x-t-when-booleanp
  (implies (booleanp x)
           (equal (if x x t)
                  t)))

(defthmd if-of-not-same-arg2
  (equal (if test (not test) else)
         (if test nil else)))

(defthm if-of-not-same-arg3
  (equal (if x y (not x))
         (if x y t)))

(defthm if-x-y-x
  (equal (if x y x)
         (if x y nil)))
