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

;rename?
;todo: reorder the syntaxp tests to fail fast
(defthm fold-consts-in-*
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (* x (* y z))
                  (* (* x y) z))))

;; todo; what if x is a constant? think about this..
(defthm *-of---arg
  (implies (syntaxp (not (quotep x))) ;prevent it from matching a constant
           (equal (* (- x) y)
                  (- (* x y))))
  :hints (("Goal" :in-theory (e/d (--BECOMES-*-OF--1)
                                  ( *-of--1)))))

(defthm *-of---arg2
  (equal (* x (- y))
         (- (* x y)))
  :hints (("Goal" :in-theory (e/d (--BECOMES-*-OF--1)
                                  ( *-of--1)))))

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

;See also <-of-*-and-*-gen below.
(defthmd <-of-*-and-*
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :hints (("Goal" :use (:instance positive
                                  (x (- x2 x1))
                                  ))))

;See also <-of-*-and-*-gen below.
(defthmd <=-of-*-and-*
  (implies (and (<= x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (<= (* x1 y) (* x2 y)))
  :hints (("Goal" :use (:instance <-of-*-and-*)
           :in-theory (disable <-of-*-and-*))))

(defthm <-of-*-and-*-gen
  (implies (and (< 0 y) ;move to conc
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (< (* x1 y) (* x2 y))
                  (< x1 x2)))
  :hints (("Goal" :cases ((< X1 X2))
           :in-theory (enable <-of-*-and-*
                              <=-of-*-and-*))))

(defthm <-of-*-cancel-2
  (implies (and (< 0 y)
                (rationalp y)
                (rationalp x))
           (equal (< (* x y) y)
                  (< x 1)))
  :hints (("Goal" :use (:instance <-of-*-and-*-gen
                                  (x1 x)
                                  (x2 1))
           :in-theory (disable <-of-*-and-*-gen))))

(defthmd <=-of-*-and-*-linear
  (implies (and (<= x1 x2)
                (< 0 y)
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (<= (* x1 y) (* x2 y)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance <-of-*-and-*)
           :in-theory (disable <-of-*-and-*))))
