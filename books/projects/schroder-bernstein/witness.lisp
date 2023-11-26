; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "SB")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "setup")
(include-book "chains")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bijective witness

(define sb-witness ((x p))
  (if (in-q-stopper (make-chain-elem t x))
      (g-inverse x)
    (f x)))


(defrule q-of-sb-witness-when-p
  (implies (p x)
           (q (sb-witness x)))
  :enable (sb-witness)
  ;; TODO: why isn't forward rule firing automatically?
  :use ((:instance has-g-inverse-when-in-q-stopper-forward
                   (x (make-chain-elem t x)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Preliminary lemmas

(defrule chain<=-when-single-chain-step
  (implies (equal (chain-step x) y)
           (chain<= x y))
  :use ((:instance chain<=-suff
                   (n 1))))

(defrule chain<=-of-f
  (chain<= (make-chain-elem t x)
           (make-chain-elem nil (f x)))
  :enable (chain-step))

(defrule chain<=-of-and-g
  (chain<= (make-chain-elem nil x)
           (make-chain-elem t (g x)))
  :enable (chain-step))

(defrule has-g-inverse-when-in-q-stopper-and-p
  (implies (and (in-q-stopper (make-chain-elem t x))
                (p x))
           (has-g-inverse x))
  :use (:instance has-g-inverse-when-in-q-stopper-forward
                  (x (make-chain-elem t x))))

(defrule chain<=-of-g-inverse-when-in-q-stopper
  (implies (and (p x)
                (in-q-stopper (make-chain-elem t x)))
           (chain<= (make-chain-elem nil (g-inverse x))
                    (make-chain-elem t x)))
  :enable (chain-step))

(defrule q-of-g-inverse-when-in-q-stopper
  (implies (and (p x)
                (in-q-stopper (make-chain-elem t x)))
           (q (g-inverse x))))

(defrule chain<=-of-f-inverse-when-not-in-q-stopper
  (implies (and (q x)
                (not (in-q-stopper (make-chain-elem nil x))))
           (chain<= (make-chain-elem t (f-inverse x))
                    (make-chain-elem nil x)))
  :enable (chain-step)
  :use (:instance has-f-inverse-when-not-in-q-stopper-forward
                  (x (make-chain-elem nil x))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Injectivity

(defruled chain=-of-sb-witness
  (implies (p x)
           (chain= (make-chain-elem t x)
                   (make-chain-elem nil (sb-witness x))))
  :cases ((in-q-stopper (make-chain-elem t x)))
  :enable (chain= sb-witness))

(defruled chain=-when-equal-sb-witness
  (implies (and (p x)
                (p y)
                (equal (sb-witness x) (sb-witness y)))
           (chain= (make-chain-elem t x)
                   (make-chain-elem t y)))
  :use ((:instance chain=-of-sb-witness
                   (x x))
        (:instance chain=-of-sb-witness
                   (x y))))


(defrule injectivity-of-sb-witness
  (implies (and (p x)
                (p y)
                (equal (sb-witness x) (sb-witness y)))
           (equal x y))
  :enable (sb-witness)
  :use chain=-when-equal-sb-witness
  :rule-classes nil
  :prep-lemmas
  ((defrule equal-g-inverse-when-has-g-inverse
     (implies (and (has-g-inverse x)
                   (has-g-inverse y))
              (equal (equal (g-inverse x) (g-inverse y))
                     (equal x y)))
     :use (:instance lemma)
     :prep-lemmas
     ((defruled lemma
        (implies (equal (g-inverse x) (g-inverse y))
                 (equal (g (g-inverse x))
                        (g (g-inverse y)))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Inverse of sb-witness (to define surjectivity)

(define is-sb-inverse (inv x)
  (and (p inv)
       (q x)
       (equal (sb-witness inv) x)))

(defchoose sb-inverse (inv) (x)
  (is-sb-inverse inv x))

(define has-sb-inverse (x)
  (is-sb-inverse (sb-inverse x) x))

(defrule p-of-sb-inverse-when-has-sb-inverse
  (implies (has-sb-inverse x)
           (p (sb-inverse x)))
  :enable (has-sb-inverse is-sb-inverse))

(defrule sb-witness-of-sb-inverse-when-has-sb-inverse
  (implies (has-sb-inverse x)
           (equal (sb-witness (sb-inverse x))
                  x))
  :enable (has-sb-inverse is-sb-inverse))

(defrule has-sb-inverse-of-sb-witness-when-p
 (implies (p x)
          (has-sb-inverse (sb-witness x)))
 :use ((:instance sb-inverse (x (sb-witness x)) (inv x)))
 :enable (has-sb-inverse
          is-sb-inverse))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Surjectivity of sb-witness

(defrule sb-witness-of-g-when-in-q-stopper
  (implies (and (q x)
                (in-q-stopper (make-chain-elem nil x)))
           (equal (sb-witness (g x)) x))
  :enable (sb-witness
           chain=)
  :use ((:instance in-q-stopper-under-chain=
                   (x (make-chain-elem nil x))
                   (y (make-chain-elem t (g x))))))

(defrule surjectivity-of-sb-witness-when-in-q-stopper
  (implies (and (q x)
                (in-q-stopper (make-chain-elem nil x)))
           (has-sb-inverse x))
  :use (:instance sb-inverse (x x) (inv (g x)))
  :enable (has-sb-inverse
           is-sb-inverse))


(defrule sb-witness-of-f-inverse-when-not-in-q-stopper
  (implies (and (q x)
                (not (in-q-stopper (make-chain-elem nil x))))
           (equal (sb-witness (f-inverse x)) x))
  :enable (sb-witness)
  :use ((:instance in-q-stopper-under-chain=
                   (x (make-chain-elem nil x))
                   (y (make-chain-elem t (f-inverse x))))
        (:instance has-f-inverse-when-not-in-q-stopper-forward
                   (x (make-chain-elem nil x)))))

(defrule surjectivity-of-sb-witness-when-not-in-q-stopper
  (implies (and (q x)
                (not (in-q-stopper (make-chain-elem nil x))))
           (has-sb-inverse x))
  :enable (has-sb-inverse
           is-sb-inverse)
  :use ((:instance has-f-inverse-when-not-in-q-stopper-forward
                   (x (make-chain-elem nil x))))
  :prep-lemmas
  ((defrule has-sb-inverse-when-equal-sb-witness-of-f-inverse
     (implies (and (q x)
                   (has-f-inverse x)
                   (equal (sb-witness (f-inverse x)) x))
              (has-sb-inverse x))
     :use (:instance sb-inverse (x x) (inv (f-inverse x)))
     :enable (has-sb-inverse
              is-sb-inverse))))


(defrule surjectivity-of-sb-witness
  (implies (q x)
           (has-sb-inverse x))
  :cases ((in-q-stopper (make-chain-elem nil x))))
