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
(local (include-book "minus"))
(local (include-book "less-than"))
(local (include-book "realpart"))
(local (include-book "imagpart"))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

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


(defthm *-of---arg1
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

(defthmd --of-*-push-into-arg1
  (equal (- (* x y))
         (* (- x) y)))

(theory-invariant (incompatible (:rewrite --of-*-push-into-arg1)
                                (:rewrite *-of---arg1)))

(defthmd --of-*-push-into-arg2
  (equal (- (* x y))
         (* x (- y))))

(theory-invariant (incompatible (:rewrite --of-*-push-into-arg2)
                                (:rewrite *-of---arg2)))

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

;; A stronger rewrite rule than <-of-*-and-*.  This is a cancellation rule.
(defthm <-of-*-and-*-cancel
  (implies (and (< 0 y) ;move to conc
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (< (* x1 y) (* x2 y))
                  (< x1 x2)))
  :hints (("Goal" :cases ((< x1 x2))
           :use ((:instance positive (x (- x2 x1)))
                 (:instance positive (x (- x1 x2)))))))



(defthm <-of-*-and-*-cancel-arg1-and-arg1
  (implies (and (< 0 y) ;move to conc
                (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (< (* y x1) (* y x2))
                  (< x1 x2)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel)
           :in-theory (disable <-of-*-and-*-cancel))))

(local
 ;; note: no rationalp hyps on x1,x2
 (defthm <-of-*-and-*-same-helper
   (implies (and (< x1 x2)
                 (< 0 y)
                 (rationalp y))
            (< (* x1 y) (* x2 y)))
   :hints (("Goal" :cases ((and (rationalp x1)
                                (rationalp x2))
                           (and (rationalp x1)
                                (complex-rationalp x2))
                           (and (rationalp x1)
                                (not (acl2-numberp x2)))
                           (and (complex-rationalp x1)
                                (rationalp x2))
                           (and (complex-rationalp x1)
                                (complex-rationalp x2))
                           (and (rationalp x1)
                                (not (acl2-numberp x2)))
                           (and (not (acl2-numberp x1))
                                (rationalp x2))
                           (and (not (acl2-numberp x1))
                                (complex-rationalp x2))
                           (and (not (acl2-numberp x1))
                                (not (acl2-numberp x2))))
            :use (:instance (:instance positive (x (- x1 x2))))
            :in-theory (enable <-when-rationalp-and-complex-rationalp
                               <-when-complex-rationalp-and-rationalp
                               <-when-complex-rationalp-and-complex-rationalp)))))

(local
 ;; note: no rationalp hyps on x1,x2
 (defthm <=-of-*-and-*-same-helper
   (implies (and (<= x1 x2)
                 (<= 0 y)
                 (rationalp y))
            (<= (* x1 y) (* x2 y)))
   :hints (("Goal" :use (:instance <-of-*-and-*-same-helper)
            :in-theory (disable <-of-*-and-*-same-helper)
            :cases ((and (rationalp x1)
                         (rationalp x2))
                    (and (rationalp x1)
                         (complex-rationalp x2))
                    (and (rationalp x1)
                         (not (acl2-numberp x2)))
                    (and (complex-rationalp x1)
                         (rationalp x2))
                    (and (complex-rationalp x1)
                         (complex-rationalp x2))
                    (and (rationalp x1)
                         (not (acl2-numberp x2)))
                    (and (not (acl2-numberp x1))
                         (rationalp x2))
                    (and (not (acl2-numberp x1))
                         (complex-rationalp x2))
                    (and (not (acl2-numberp x1))
                         (not (acl2-numberp x2))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Experience has shown that we need both the :forward-chaining rules and the
;; :linear rules about whose names start with <-of-*-and-*-same.

;; When considering a product, if the first argument is bounded above, add a
;; bound on the product.
(defthm <-of-*-and-*-same-forward-1
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes ((:forward-chaining :trigger-terms ((* x1 y)))))

;; When considering a product, if the first argument is bounded below, add a
;; bound on the product.
(defthm <-of-*-and-*-same-forward-2
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes ((:forward-chaining :trigger-terms ((* x2 y))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-forward-1))))

;; When considering a product, if the second argument is bounded above, add a
;; bound on the product.
(defthm <-of-*-and-*-same-forward-3
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes ((:forward-chaining :trigger-terms ((* y x1))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-forward-1))))

;; When considering a product, if the second argument is bounded below, add a
;; bound on the product.
(defthm <-of-*-and-*-same-forward-4
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes ((:forward-chaining :trigger-terms ((* y x2))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-forward-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; When considering a product, if the first argument is bounded above, add a
;; bound on the product.
(defthm <-of-*-and-*-same-linear-1
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes ((:linear :trigger-terms ((* x1 y)))))

;; When considering a product, if the first argument is bounded below, add a
;; bound on the product.
(defthm <-of-*-and-*-same-linear-2
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* x1 y) (* x2 y)))
  :rule-classes ((:linear :trigger-terms ((* x2 y))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear-1))))

;; When considering a product, if the second argument is bounded above, add a
;; bound on the product.
(defthm <-of-*-and-*-same-linear-3
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes ((:linear :trigger-terms ((* y x1))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear-1))))

;; When considering a product, if the second argument is bounded below, add a
;; bound on the product.
(defthm <-of-*-and-*-same-linear-4
  (implies (and (< x1 x2)
                (< 0 y)
                (rationalp y))
           (< (* y x1) (* y x2)))
  :rule-classes ((:linear :trigger-terms ((* y x2))))
  :hints (("Goal" :use (:instance <-of-*-and-*-same-linear-1))))

(deftheory <-of-*-and-*-same-linear
  '(<-of-*-and-*-same-linear-1
    <-of-*-and-*-same-linear-2
    <-of-*-and-*-same-linear-3
    <-of-*-and-*-same-linear-4)
  :redundant-okp t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm <=-of-*-and-*-same-forward-1
  (implies (and (<= x1 x2)
                (<= 0 y)
                (rationalp y))
           (<= (* x1 y) (* x2 y)))
  :hints (("Goal" :cases ((equal 0 y))))
  :rule-classes ((:forward-chaining :trigger-terms ((* x1 y)))))

(defthm <=-of-*-and-*-same-forward-2
  (implies (and (<= x1 x2)
                (<= 0 y)
                (rationalp y))
           (<= (* x1 y) (* x2 y)))
  :rule-classes ((:forward-chaining :trigger-terms ((* x2 y))))
  :hints (("Goal" :use (:instance <=-of-*-and-*-same-forward-1))))

(defthm <=-of-*-and-*-same-forward-3
  (implies (and (<= x1 x2)
                (<= 0 y)
                (rationalp y))
           (<= (* y x1) (* y x2)))
  :rule-classes ((:forward-chaining :trigger-terms ((* y x1))))
  :hints (("Goal" :use (:instance <=-of-*-and-*-same-forward-1))))

(defthm <=-of-*-and-*-same-forward-4
  (implies (and (<= x1 x2)
                (<= 0 y)
                (rationalp y))
           (<= (* y x1) (* y x2)))
  :rule-classes ((:forward-chaining :trigger-terms ((* y x2))))
  :hints (("Goal" :use (:instance <=-of-*-and-*-same-forward-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; See also <-of-*-and-*-cancel (which should fire as a rewrite rule -- recall
;; that <= is a negated call to <), but this one may be more suitable for use
;; in hints.  Gives rise to two linear rules, each with a free var.
(defthm <=-of-*-and-*-same-linear
  (implies (and (<= x1 x2)
                (< 0 y)
                (rationalp y))
           (<= (* x1 y) (* x2 y)))
  :rule-classes :linear)

;; Commuted version of <=-of-*-and-*-same-linear.
(defthm <=-of-*-and-*-same-alt-linear
  (implies (and (<= x1 x2)
                (< 0 y)
                (rationalp y))
           (<= (* y x1) (* y x2)))
  :hints (("Goal" :use (:instance <=-of-*-and-*-same-linear)
           :in-theory (disable <=-of-*-and-*-same-linear)))
  :rule-classes :linear)

(defthm <-of-*-cancel-1
  (implies (and (< 0 y)
                (rationalp y)
                (rationalp x))
           (equal (< y (* x y))
                  (< 1 x)))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x1 1)
                                  (x2 x))
           :in-theory (disable <-of-*-and-*-cancel))))

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

(defthm <-of-*-same-arg2
  (implies (and (<= 0 x)
                (rationalp y)
                (rationalp x))
           (equal (< x (* x y))
                  (if (equal x 0)
                      nil
                    (< 1 y))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x1 1)
                                  (x2 y)
                                  (y x))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <-of-*-same-arg3
  (implies (and (<= 0 x)
                (rationalp y)
                (rationalp x))
           (equal (< (* x y) x)
                  (if (equal x 0)
                      nil
                    (< y 1))))
  :hints (("Goal" :use (:instance <-of-*-and-*-cancel
                                  (x1 y)
                                  (x2 1)
                                  (y x))
           :in-theory (disable <-of-*-and-*-cancel))))

(defthm <-of-*-same-linear-special
  (implies (and (< 1 y)
                (< 0 x)
                (rationalp x)
                (rationalp y))
           (< x (* x y)))
  :rule-classes :linear
  :hints (("Goal" :use (:instance <-of-*-and-*-same-forward-1 (x1 1) (x2 y) (y x))
           :in-theory (disable <-of-*-and-*-same-forward-1))))

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

;; The proof given here avoids needing the book about /.
(defthm equal-of-*-and-constant
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (< 0 k2) ;gen
                )
           (equal (equal k1 (* k2 x))
                  (and (acl2-numberp k1)
                       (equal (/ k1 k2) (fix x)))))
  :hints (("Goal" :in-theory (disable inverse-of-*
                                      associativity-of-*)
           :use ((:instance inverse-of-* (x k2))
                 (:instance associativity-of-* (x k2) (y (/ k2)) (z x))))))

(defthmd *-both-sides
  (implies (equal x y)
           (equal (* z x) (* z y))))

;; not exported here because it mentions /
(local
 (defthm *-of-/-same-arg2
   (equal (* x (/ x) y)
          (if (equal 0 (fix x))
              0
            (fix y)))
   :hints (("Goal" :in-theory (disable associativity-of-*
                                       commutativity-2-of-*)
            :use (:instance associativity-of-* (y (/ x)) (z y))))))

(defthm equal-of-*-and-*-cancel
  (equal (equal (* x y) (* x z))
         (or (equal (fix x) 0)
             (equal (fix y) (fix z))))
  :hints (("Goal" :use (:instance *-both-sides
                                  (x (* x y))
                                  (y (* x z))
                                  (z (/ x))))))

(defthm equal-of-*-and-*-cancel-arg2-arg2
  (equal (equal (* y x) (* z x))
         (or (equal (fix x) 0)
             (equal (fix y) (fix z))))
  :hints (("Goal" :use (:instance *-both-sides
                                  (x (* x y))
                                  (y (* x z))
                                  (z (/ x))))))

(defthm <-of-*-and-*-cancel-gen
  (implies (and (rationalp x1)
                (rationalp x2)
                (rationalp y))
           (equal (< (* x1 y) (* x2 y))
                  (if (< 0 y)
                      (< x1 x2)
                    (if (equal 0 y)
                        nil
                      (< x2 x1)))))
  :hints (("Goal" :use ((:instance <-of-*-and-*-cancel)
                        (:instance <-of-*-and-*-cancel (y (- y))))
           :in-theory (disable <-of-*-and-*-cancel))))
