; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book deals with inverses of relational and functional composition.

(in-package "ZF")

(include-book "set-algebra")

(encapsulate ()

(local
 (defthmz inverse-rcompose-inverse-lemma
   (implies (in-rcompose (cons x y) r s)
            (in-rcompose (cons y x) (inverse s) (inverse r)))
   :hints (("Goal"
            :expand ((in-rcompose (cons x y) r s))
            :in-theory (disable in-rcompose)
            :use
            ((:instance
              in-rcompose-suff
              (p1 (cons (cdr (mv-nth 1
                                     (in-rcompose-witness (cons x y) r s)))
                        (car (mv-nth 1
                                     (in-rcompose-witness (cons x y) r s)))))
              (p2 (cons (cdr (car (in-rcompose-witness (cons x y) r s)))
                        (car (car (in-rcompose-witness (cons x y) r s)))))
              (p (cons y x))
              (r (inverse s))
              (s (inverse r))))))
   :props (zfc prod2$prop inverse$prop)))

(defthmz inverse-rcompose-inverse
  (implies (and (in-rcompose pair2 r s)
                (equal pair2
                       (cons (cdr pair) (car pair)))
                (consp pair))
           (in-rcompose pair (inverse s) (inverse r)))
  :props (zfc prod2$prop inverse$prop))
)

(defthmz inverse-rcompose-1
  (subset (inverse (rcompose r s))
          (rcompose (inverse s) (inverse r)))
  :hints (("Goal"
           :expand ((subset (inverse (rcompose r s))
                            (rcompose (inverse s) (inverse r))))))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop))

(defthm in-rcompose-implies-consp
  (implies (in-rcompose p r s)
           (consp p))
  :hints (("Goal" :in-theory (enable in-rcompose)))
  :rule-classes :forward-chaining)

(defthmz inverse-rcompose-2
  (implies (and (relation-p r)
                (relation-p s))
           (subset (rcompose (inverse s) (inverse r))
                   (inverse (rcompose r s))))
  :hints
  (("Goal"
    :expand ((subset (rcompose (inverse s) (inverse r))
                     (inverse (rcompose r s))))
    :in-theory (disable inverse-rcompose-inverse)
    :use
    ((:instance
      inverse-rcompose-inverse
      (pair
       (cons (cdr (subset-witness (rcompose (inverse s)
                                            (inverse r))
                                  (inverse (rcompose r s))))
             (car (subset-witness (rcompose (inverse s)
                                            (inverse r))
                                  (inverse (rcompose r s))))))
      (pair2
       (cons (car (subset-witness (rcompose (inverse s)
                                            (inverse r))
                                  (inverse (rcompose r s))))
             (cdr (subset-witness (rcompose (inverse s)
                                            (inverse r))
                                  (inverse (rcompose r s))))))
      (r (inverse s))
      (s (inverse r))))))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop))

(defthmz inverse-rcompose
  (implies (and (relation-p r)
                (relation-p s))
           (equal (inverse (rcompose r s))
                  (rcompose (inverse s) (inverse r))))
  :hints
  (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc prod2$prop rcompose$prop domain$prop inverse$prop))

; A next goal is a corollary of inverse-rcompose for functions.

(defthmz apply-apply-inverse ; to prove image-inverse-1
  (implies (and (funp f)
                (in x (image f)))
           (equal (apply f (apply (inverse f) x))
                  x))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz image-inverse-1
  (subset (image (inverse r))
          (domain r))
  :hints (("Goal"
           :expand ((subset (domain (inverse (inverse r)))
                            (domain r)))
           :in-theory (e/d (image in-domain-rewrite)
                           (in-cons-apply))))
  :props (zfc prod2$prop inverse$prop domain$prop))

(defthmz image-inverse-2
  (subset (domain r)
          (image (inverse r)))
  :hints (("Goal"
           :expand ((subset (domain r)
                            (domain (inverse (inverse r)))))
           :in-theory (enable image)
           :restrict
           ((in-car-domain-alt
             ((p (cons (subset-witness
                        (domain r)
                        (domain (inverse (inverse r))))
                       (apply r
                              (subset-witness
                               (domain r)
                               (domain (inverse (inverse r))))))))))))
  :props (zfc prod2$prop inverse$prop domain$prop))

(defthmz image-inverse
; The following can be proved easily, without the two lemmas just above and
; without domain$prop, if we add a (relation-p r) hypothesis.
  (equal (image (inverse r))
         (domain r))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc prod2$prop inverse$prop domain$prop))

(defthmz domain-inverse
  (equal (domain (inverse r))
         (image r))
  :hints (("Goal" :in-theory (enable image)))
  :props (zfc prod2$prop inverse$prop))

(defthmz inverse-compose-weak
  (implies (and (funp g)
                (funp f)
                (subset (image g) (domain f)))
           (equal (inverse (compose f g))
                  (rcompose (inverse f) (inverse g))))
  :hints
  (("Goal"
    :in-theory (disable inverse-rcompose)
    :use ((:instance inverse-rcompose (r g) (s f)))))
  :props (zfc prod2$prop rcompose$prop compose$prop domain$prop inverse$prop))

(defthmz inverse-compose-strong
  (implies (and (injective-funp g)
                (injective-funp f)
                (equal (image g) (domain f)))
           (equal (inverse (compose f g))
                  (compose (inverse g) (inverse f))))
  :props (zfc prod2$prop rcompose$prop compose$prop domain$prop inverse$prop))
