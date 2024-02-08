; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

(in-package "SBT")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "setup"))
(local (include-book "witness"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Setup

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conclusion

(encapsulate
  (((sb *) => *))

  (local
   ;; Our constructed bijection
   (define sb ((x p))
     (if (in-q-stopper (make-chain-elem t x))
         (g-inverse x)
       (f x))))

  (define-sk exists-sb-inverse (x)
    ;; Guard verified below (otherwise encapsulate complains that guard
    ;; verification may depend on local porperties)
    :verify-guards nil
    (exists inv
            (and (p inv)
                 (equal (sb inv) x))))

  (defrule q-of-sb-when-p
    (implies (p x)
             (q (sb x)))
    :enable (sb sb-witness)
    :use q-of-sb-witness-when-p)

  (defrule injectivity-of-sb
    (implies (and (p x)
                  (p y)
                  (equal (sb x) (sb y)))
             (equal x y))
    :enable (sb sb-witness)
    :use injectivity-of-sb-witness
    :rule-classes nil)

  (defrule surjectivity-of-sb
    (implies (q x)
             (exists-sb-inverse x))
    :use ((:instance surjectivity-of-sb-witness)
          (:instance exists-sb-inverse-when-has-sb-inverse))
    :prep-lemmas
    ((defrule exists-sb-inverse-when-has-sb-inverse
       (implies (has-sb-inverse x)
                (exists-sb-inverse x))
       :enable (has-sb-inverse
                is-sb-inverse
                sb
                sb-witness)
       :use ((:instance exists-sb-inverse-suff
                        (inv (sb-inverse x))
                        (x x)))))))


(verify-guards exists-sb-inverse)
