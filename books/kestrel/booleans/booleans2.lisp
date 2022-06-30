; Theorems about mynot and xor
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "booleans") ;reduce?

(defthm xor-associative
  (implies (and (booleanp a)
                (booleanp b)
                (booleanp c))
           (equal (xor (xor a b) c)
                  (xor a (xor b c))))
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-nil
  (implies (booleanp x)
           (equal (xor nil x)
                  x)))

;We have this because we can disable it.
(defund mynot (x)
  (not x))

(defthm xor-t
  (implies (booleanp x)
           (equal (xor t x)
                  (mynot x)))
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm mynot-mynot
  (implies (booleanp x)
           (equal (mynot (mynot x))
                  x))
  :hints (("Goal" :in-theory (enable mynot))))

(defthm xor-of-mynot-1
  (equal (xor (mynot a) b)
         (mynot (xor a b)))
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-of-mynot-2
  (equal (xor b (mynot a))
         (mynot (xor b a)))
  :hints (("Goal" :in-theory (enable xor mynot))))

;yuck?!
(defthm xor-when-equal
  (implies (equal x y)
           (equal (xor x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

;or should we rewrite the order of equal?
(defthm xor-equal-hack
  (equal (xor (equal x y) (equal y x))
         nil)
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-combine-constants
  (implies (syntaxp (and (quotep a) (quotep b)))
           (equal (xor a (xor b c))
                  (xor (xor a b) c)))
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-same
  (implies (booleanp b)
           (equal (xor a (xor a b))
                  b))
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-same-simple
  (equal (xor a a)
         nil)
  :hints (("Goal" :in-theory (enable xor))))

(defthm xor-mynot
  (equal (xor x (mynot x))
         t)
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-mynot-2
  (equal (xor (mynot x) x)
         t)
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-mynot-alt
  (equal (xor x (xor (mynot x) y))
         (mynot y))
  :hints (("Goal" :in-theory (enable xor mynot))))

(defthm xor-mynot-alt2
  (equal (xor (mynot x) (xor x y))
         (mynot y))
  :hints (("Goal" :in-theory (enable xor mynot))))
