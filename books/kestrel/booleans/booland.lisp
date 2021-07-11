; A book about booland (boolean-valued conjunction)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: In-progress

(include-book "bool-fix")

(defund booland (x y)
  (declare (xargs :guard t))
  (if x (if y t nil) nil))

(defthm booleanp-of-booland
  (booleanp (booland x y))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-associative
  (equal (booland (booland x y) z)
         (booland x (booland y z)))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-commutative
  (equal (booland x y)
         (booland y x))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-commutative-2
  (equal (booland x (booland y z))
         (booland y (booland x z)))
  :hints (("Goal" :in-theory (enable booland))))

;drop, since we know how to handle constants?
(defthm booland-combine-constants
  (implies (syntaxp (and (quotep a) (quotep b)))
           (equal (booland a (booland b c))
                  (booland (booland a b) c))))

;drop?
(defthmd booland-commute-constant
  (implies (syntaxp (and (quotep y)
                         (not (quotep x))))
           (equal (booland x y)
                  (booland y x))))

;what about of something other than t or nil?
(defthm booland-of-t
  (equal (booland t x)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-of-non-nil
  (implies (and (syntaxp (quotep k))
                k)
           (equal (booland k x)
                  (bool-fix x)))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-of-non-nil-arg2
  (implies (and (syntaxp (quotep k))
                k)
           (equal (booland x k)
                  (bool-fix x)))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-of-nil-arg1
  (equal (booland nil x)
         nil)
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-of-nil-arg2
  (equal (booland x nil)
         nil)
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-same
  (equal (booland x x)
         (bool-fix x))
  :hints (("Goal" :in-theory (enable booland))))

(defthm booland-same-2
  (equal (booland x (booland x y))
         (booland x y))
  :hints (("Goal" :in-theory (enable booland))))

;; Helps justify the STP translation.
(defthm booland-of-bool-fix-arg1
  (equal (booland (bool-fix x) y)
         (booland x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline booland))))

;; Helps justify the STP translation.
(defthm booland-of-bool-fix-arg2
  (equal (booland x (bool-fix y))
         (booland x y))
  :hints (("Goal" :in-theory (enable bool-fix$inline booland))))

;; These help justify some things that Axe does:
(defcong iff equal (booland x y) 1 :hints (("Goal" :in-theory (enable booland))))
(defcong iff equal (booland x y) 2 :hints (("Goal" :in-theory (enable booland))))
