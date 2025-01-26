; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SBT")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "chains")
(include-book "definverse")
(include-book "setup")

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Bijective witness

(define sb-witness ((x p))
  (if (in-q-stopper (chain-elem t x))
      (g-inverse x)
    (f x)))

(defrule q-of-sb-witness-when-p
  (implies (p x)
           (q (sb-witness x)))
  :enable sb-witness
  :use (:instance in-g-imagep-when-in-q-stopper
                  (elem (chain-elem t x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Preliminary lemmas

;; MOVE stuff in this section

(defrule chain<=-when-single-chain-step
  (implies (equal (chain-step x) y)
           (chain<= x y))
  :enable chain-steps
  :use ((:instance chain<=-suff
                   (n 1))))

(defrule chain<=-of-f
  (chain<= (chain-elem t x)
           (chain-elem nil (f x)))
  :enable chain-step)

(defrule chain<=-of-and-g
  (chain<= (chain-elem nil x)
           (chain-elem t (g x)))
  :enable (chain-step))

(defrule in-g-imagep-when-in-q-stopper-and-p
  (implies (and (in-q-stopper (chain-elem t x))
                (p x))
           (in-g-imagep x))
  :use (:instance in-g-imagep-when-in-q-stopper
                  (elem (chain-elem t x))))

(defrule chain<=-of-g-inverse-when-in-q-stopper
  (implies (and (p x)
                (in-q-stopper (chain-elem t x)))
           (chain<= (chain-elem nil (g-inverse x))
                    (chain-elem t x)))
  :enable chain-step)

(defrule q-of-g-inverse-when-in-q-stopper
  (implies (and (p x)
                (in-q-stopper (chain-elem t x)))
           (q (g-inverse x))))

(defrule chain<=-of-f-inverse-when-not-in-q-stopper
  (implies (and (q x)
                (not (in-q-stopper (chain-elem nil x))))
           (chain<= (chain-elem t (f-inverse x))
                    (chain-elem nil x)))
  :enable chain-step
  :use (:instance in-f-imagep-when-not-in-q-stopper
                  (elem (chain-elem nil x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Injectivity

(defruled chain=-of-sb-witness
  (implies (p x)
           (chain= (chain-elem t x)
                   (chain-elem nil (sb-witness x))))
  :enable (chain= sb-witness)
  :cases ((in-q-stopper (chain-elem t x))))

(defruled chain=-when-equal-sb-witness
  (implies (and (p x)
                (p y)
                (equal (sb-witness x) (sb-witness y)))
           (chain= (chain-elem t x)
                   (chain-elem t y)))
  :use ((:instance chain=-of-sb-witness
                   (x x))
        (:instance chain=-of-sb-witness
                   (x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule injectivity-of-sb-witness
  (implies (and (p x)
                (p y)
                (equal (sb-witness x)
                       (sb-witness y)))
           (equal x y))
  :rule-classes nil
  :enable sb-witness
  :use chain=-when-equal-sb-witness
  :prep-lemmas
  ((defrule equal-g-inverse-when-in-g-imagep
     (implies (and (in-g-imagep x)
                   (in-g-imagep y))
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

;; TODO
;; (definverse sb-witness
;;   :domain p
;;   :codomain q)

(define is-sb-inverse (inv x)
  (and (p inv)
       (q x)
       (equal (sb-witness inv) x)))

(defchoose sb-inverse (inv) (x)
  (is-sb-inverse inv x))

(define in-sb-imagep (x)
  (is-sb-inverse (sb-inverse x) x))

(defrule p-of-sb-inverse-when-in-sb-imagep
  (implies (in-sb-imagep x)
           (p (sb-inverse x)))
  :enable (in-sb-imagep is-sb-inverse))

(defrule sb-witness-of-sb-inverse-when-in-sb-imagep
  (implies (in-sb-imagep x)
           (equal (sb-witness (sb-inverse x))
                  x))
  :enable (in-sb-imagep is-sb-inverse))

(defrule in-sb-imagep-of-sb-witness-when-p
 (implies (p x)
          (in-sb-imagep (sb-witness x)))
 :enable (in-sb-imagep
           is-sb-inverse)
 :use (:instance sb-inverse (x (sb-witness x)) (inv x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Surjectivity of sb-witness

(defrule sb-witness-of-g-when-in-q-stopper
  (implies (and (q x)
                (in-q-stopper (chain-elem nil x)))
           (equal (sb-witness (g x)) x))
  :enable (sb-witness
           chain=)
  :use (:instance in-q-stopper-under-chain=
                  (x (chain-elem nil x))
                  (y (chain-elem t (g x)))))

(defrule surjectivity-of-sb-witness-when-in-q-stopper
  (implies (and (q x)
                (in-q-stopper (chain-elem nil x)))
           (in-sb-imagep x))
  :enable (in-sb-imagep
           is-sb-inverse)
  :use (:instance sb-inverse (x x) (inv (g x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule sb-witness-of-f-inverse-when-not-in-q-stopper
  (implies (and (q x)
                (not (in-q-stopper (chain-elem nil x))))
           (equal (sb-witness (f-inverse x)) x))
  :enable sb-witness
  :use ((:instance in-q-stopper-under-chain=
                   (x (chain-elem nil x))
                   (y (chain-elem t (f-inverse x))))
        (:instance in-f-imagep-when-not-in-q-stopper
                   (elem (chain-elem nil x)))))

(defrule surjectivity-of-sb-witness-when-not-in-q-stopper
  (implies (and (q x)
                (not (in-q-stopper (chain-elem nil x))))
           (in-sb-imagep x))
  :enable (in-sb-imagep
           is-sb-inverse)
  :use (:instance in-f-imagep-when-not-in-q-stopper
                  (elem (chain-elem nil x)))
  :prep-lemmas
  ((defrule in-sb-imagep-when-equal-sb-witness-of-f-inverse
     (implies (and (q x)
                   (in-f-imagep x)
                   (equal (sb-witness (f-inverse x)) x))
              (in-sb-imagep x))
     :enable (in-sb-imagep
              is-sb-inverse)
     :use (:instance sb-inverse (x x) (inv (f-inverse x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule surjectivity-of-sb-witness
  (implies (q x)
           (in-sb-imagep x))
  :cases ((in-q-stopper (chain-elem nil x))))
