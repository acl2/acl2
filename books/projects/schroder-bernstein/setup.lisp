; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "SBT")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((f *) => *)
   ((g *) => *)
   ((p *) => *)
   ((q *) => *))

  (local (define p (x) (declare (ignore x)) :enabled t t))
  (local (define q (x) (declare (ignore x)) :enabled t t))

  (local (define f (x) :enabled t x))
  (local (define g (x) :enabled t x))

  (defrule q-of-f-when-p
    (implies (p x)
             (q (f x))))

  (defrule injectivity-of-f
    (implies (and (p x)
                  (p y)
                  (equal (f x) (f y)))
             (equal x y))
    :rule-classes nil)

  (defrule p-of-g-when-q
    (implies (q x)
             (p (g x))))

  (defrule injectivity-of-g
    (implies (and (q x)
                  (q y)
                  (equal (g x) (g y)))
             (equal x y))
    :rule-classes nil))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Injective rules

(defrule equal-of-f-and-f
  (implies (and (p x)
                (p y))
           (equal (equal (f x) (f y))
                  (equal x y)))
  :use injectivity-of-f)

(defrule equal-of-g-and-g
  (implies (and (q x)
                (q y))
           (equal (equal (g x) (g y))
                  (equal x y)))
  :use injectivity-of-g)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inverses

(define is-f-inverse (inv x)
  (and (p inv)
       (q x)
       (equal (f inv) x)))

(defchoose f-inverse (inv) (x)
  (is-f-inverse inv x))

(define has-f-inverse (x)
  (is-f-inverse (f-inverse x) x))


(defrule p-of-f-inverse-when-has-f-inverse
  (implies (has-f-inverse x)
           (p (f-inverse x)))
  :enable (has-f-inverse is-f-inverse))

(defrule f-of-f-inverse-when-has-f-inverse
  (implies (has-f-inverse x)
           (equal (f (f-inverse x))
                  x))
  :enable (has-f-inverse is-f-inverse))

(defrule f-inverse-of-f-when-p
  (implies (p x)
           (equal (f-inverse (f x))
                  x))
  :use ((:instance f-inverse (inv x) (x (f x))))
  :enable (is-f-inverse))

(defrule has-f-inverse-of-f-when-p
 (implies (p x)
          (has-f-inverse (f x)))
 :enable (has-f-inverse
          is-f-inverse))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define is-g-inverse (inv x)
  (and (q inv)
       (p x)
       (equal (g inv) x)))

(defchoose g-inverse (inv) (x)
  (is-g-inverse inv x))

(define has-g-inverse (x)
  (is-g-inverse (g-inverse x) x))


(defrule q-of-g-inverse-when-has-g-inverse
  (implies (has-g-inverse x)
           (q (g-inverse x)))
  :enable (has-g-inverse is-g-inverse))

(defrule g-of-g-inverse-when-has-g-inverse
  (implies (has-g-inverse x)
           (equal (g (g-inverse x))
                  x))
  :enable (has-g-inverse is-g-inverse))

(defrule g-inverse-of-g-when-q
  (implies (q x)
           (equal (g-inverse (g x))
                  x))
  :use ((:instance g-inverse (inv x) (x (g x))))
  :enable (is-g-inverse))

(defrule has-g-inverse-of-g-when-q
 (implies (q x)
          (has-g-inverse (g x)))
 :enable (has-g-inverse
          is-g-inverse))
