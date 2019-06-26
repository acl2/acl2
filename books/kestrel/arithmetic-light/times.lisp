; A lightweight book about the built-in operation *.
;
; Copyright (C) 2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "plus"))

; note that the rules associativity-of-*, commutativity-of-*, and unicity-of-1
; are built in to ACL2.

(defthm integerp-of-*
  (implies (and (integerp x)
                (integerp y))
           (integerp (* x y))))

(defthm equal-of-0-and-*
  (equal (equal 0 (* x y))
         (or (equal 0 (fix x))
             (equal 0 (fix y)))))

(defthm *-of-0
  (equal (* 0 x)
         0))

(defthm commutativity-2-of-*
  (equal (* x (* y z))
         (* y (* x z)))
  :hints (("Goal" :use ((:instance associativity-of-*)
                        (:instance associativity-of-* (x y) (y x)))
           :in-theory (disable associativity-of-*))))

(defthm *-of-*-combine-constants
  (implies (and (syntaxp (quotep y)) ;tested first to fail fast
                (syntaxp (quotep x)))
           (equal (* x (* y z))
                  (* (* x y) z))))

;; NORMAL FORM: We have a choice between two equivalent ways to express
;; negation: (- x) and (* -1 x).  At least for now, we prefer (- x), for
;; compatibility with our existing development.

(defthm *-of--1
  (equal (* -1 x)
         (- x)))

(defthmd --becomes-*-of--1
  (equal (- x)
         (* -1 x)))

(theory-invariant (incompatible (:rewrite *-of--1) (:rewrite --becomes-*-of--1)))

(defthmd integerp-of-*-three
  (implies (and (integerp (* x y))
                (integerp z))
           (integerp (* x y z)))
  :hints (("Goal" :use (:instance integerp-of-*
                                  (x (* x y))
                                  (y z))
           :in-theory (disable integerp-of-*))))


(defthm *-of---arg
  (implies (syntaxp (not (quotep x))) ;prevent it from matching a constant
           (equal (* (- x) y)
                  (- (* x y))))
  :hints (("Goal" :in-theory (e/d (--becomes-*-of--1)
                                  (*-of--1)))))

(defthm *-of---arg2
  (equal (* x (- y))
         (- (* x y)))
  :hints (("Goal" :in-theory (e/d (--becomes-*-of--1)
                                  (*-of--1)))))

(defthm <-of-*-and-0
  (implies (and (rationalp x)
                (rationalp y))
           (equal (< (* x y) 0)
                  (or (and (< x 0)
                           (< 0 y))
                      (and (< y 0)
                           (< 0 x)))))
  :hints (("Goal" :cases ((< x 0)
                          (and (< 0 X) (< Y 0))
                          (and (< 0 X) (< 0 Y))))))

;; See also <-of-*-and-*-cancel, but this one may be more suitable for use in
;; hints.  Gives rise to two linear rules, each with a free var.
(defthm <-of-*-and-*-same-linear
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance positive (x (- x2 x1))))))

;; Commuted version of <-of-*-and-*-same-linear.
(defthm <-of-*-and-*-same-alt-linear
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear)
           :in-theory (disable <-of-*-and-*-same-linear))))

;; This can sometimes get the proof when the linear rules does not, but we
;; leave it disabled by default for speed.
(defthmd <-of-*-and-*-same-forward-1
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes ((:forward-chaining :trigger-terms ((* x1 y))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear))))

;; This can sometimes get the proof when the linear rules does not, but we
;; leave it disabled by default for speed.
(defthmd <-of-*-and-*-same-forward-2
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes ((:forward-chaining :trigger-terms ((* x2 y))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear))))

;; This can sometimes get the proof when the linear rules does not, but we
;; leave it disabled by default for speed.
(defthmd <-of-*-and-*-same-alt-forward-1
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes ((:forward-chaining :trigger-terms ((* y x1))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-alt-linear))))

;; This can sometimes get the proof when the linear rules does not, but we
;; leave it disabled by default for speed.
(defthmd <-of-*-and-*-same-alt-forward-2
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes ((:forward-chaining :trigger-terms ((* y x2))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-alt-linear))))

;; A stronger rewrite rule than <-of-*-and-*.  This is a cancellation rule.
(defthm <-of-*-and-*-cancel
  (implies (and (< 0 y) ;move to conc
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (< (* x1 y) (* x2 y))
                  (< x1 x2)))
  :hints (("Goal" :use (<-of-*-and-*-same-linear
                        (:instance <-of-*-and-*-same-linear (x1 x2) (x2 x1))))))

;; See also <-of-*-and-*-cancel (which should fire when this does, recall that
;; <= is a negated call to <), but this one may be more suitable for use in
;; hints.  Gives rise to two linear rules, each with a free var.
(defthm <=-of-*-and-*-same-linear
  (implies (and (<= x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (<= (* x1 y) (* x2 y)))
  :rule-classes :linear)

;; Commuted version of <=-of-*-and-*-same-linear.
(defthm <=-of-*-and-*-same-alt-linear
  (implies (and (<= x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (<= (* y x1) (* y x2)))
  :hints (("Goal" :use (:instance <=-of-*-and-*-same-linear)
           :in-theory (disable <=-of-*-and-*-same-linear)))
  :rule-classes :linear)

(defthm <-of-*-cancel-2
  (implies (and (< 0 y)
                (rationalp y)
                (rationalp x))
           (equal (< (* x y) y)
                  (< x 1)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x1 x)
                                  (x2 1))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <-of-*-same-linear-special
  (implies (and (< 1 y)
                (< 0 x)
                (rationalp x)
                (rationalp y))
           (< x (* x y)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear (x1 1) (x2 y) (y x))
           :in-theory (disable <-of-*-and-*-same-linear))))

(defthm <-of-*-and-*
  (implies (and (< x1 x2) ; strict
                (<= y1 y2) ; weak
                (<= 0 x1)
                (< 0 y1)
                (rationalp x1)
                (rationalp x2)
                (rationalp y1)
                (rationalp y2))
           (< (* x1 y1) (* x2 y2)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use ((:instance <=-of-*-and-*-same-linear
                                   (x1 y1)
                                   (x2 y2)
                                   (y x2)))
           :in-theory (disable <-of-*-and-*-cancel))))
