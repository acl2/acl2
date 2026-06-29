; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../inverse")
(include-book "base")
(include-book "../zfns")

(defthmz subset-preserves-in-in
  (implies (and (in-in x s1)
                (subset s1 s2))
           (in-in x s2))
  :hints (("Goal"
           :expand ((in-in x s1)))))

(defthmz in-domain-implies-in-in-union
  (implies (in x (domain f))
           (in-in x (union f)))
  :hints (("Goal"
           :restrict ((in-in-suff
                       ((a (pair x x))
                        (y (cons x (apply f x)))
                        (x f))
                       ((a x)
                        (y (pair x x))
                        (x (union f)))))
           :use ((:instance cons-as-ordered-pair
                            (x x)
                            (y (apply f x))))))
  :props (zfc domain$prop))

(defthmz finite-implies-finite-domain-1-1
  (implies (and (subset f (image g))
                (funp g)
                (in x (domain f)))
           (in x (image (compose (zcar (image g))
                                 g))))
  :hints (("Goal"
           :in-theory (disable in-image-suff)
           :use ((:instance
                  in-image-suff
                  (y x)
                  (r (zcar (image g)))
                  (p (cons (cons x (apply f x)) x)))
                 (:instance
                  in-image-suff
                  (y x)
                  (r (compose (zcar (image g)) g))
                  (p (cons (apply (inverse g) (cons x (apply f x)))
                           x))))))
  :props (zfns-prop compose$prop))

(defthmz finite-implies-finite-domain-1
  (implies (and (funp g)
                (subset f (image g)))
           (subset (domain f)
                   (image (compose (zcar (image g))
                                   g))))
  :hints (("Goal" :expand ((subset (domain f)
                                   (image (compose (zcar (image g))
                                                   g))))))
  :props (zfns-prop compose$prop))

(defthmdz finite-implies-finite-domain

; Proof sketch.  f is finite, there is a function g mapping some natural number
; n onto f.  Then (compose (zcar (image g)) g) maps n onto (domain f).

  (implies (finite f)
           (finite (domain f)))
  :hints (("Goal"
           :expand ((finite f))
           :restrict ((finite-suff
                       ((f (compose (zcar (image (finite-witness f)))
                                    (finite-witness f))))))
           :use ((:instance finite-implies-finite-domain-1
                            (g (finite-witness f))))))
  :props (zfns-prop compose$prop))

; Start proof of finite-domain-implies-finite.

(include-book "../identity")
(include-book "../phoenix")

(local (defun fdif (f g)

; This helper function's name is based on finite-domain-implies-finite, where
; it is used in a hint.  Suppose g maps n onto the domain of f.  We want to
; build a function that maps n onto f, which we can do by mapping k < n to
; (cons g(k) (f (g k))).  Let I = (identity-fun (prod2 (image g) (image+ f)).
; Then we are mapping k < n to (apply I (cons (apply g k) (apply (compose f g)
; k))) = (apply (phoenix I g (compose f g)) k).

         (phoenix (identity-fun (prod2 (image g) (image+ f)))
                  g
                  (compose f g))))

(local
 (defthmz finite-domain-implies-finite-1-1

; Sketch of proof.  Assume the hyps and write x as <a b>.  Choose n such that a
; = g(n).  Let P be the phoenix call below.  Then P(n) = I(<(g(n),f(g(n)))>)
; = <a,f(a)> = <a,b> = x, so x \in image(P).

   (implies
    (and (funp f)
         (funp g)
         (subset (domain f) (image g))
         (in x f))
    (in x
        (image (phoenix
                (identity-fun (union2 (prod2 (image g) (pair 0 0))
                                      (prod2 (image g) (image f))))
                g
                (compose f g)))))
   :hints (("Goal"
            :restrict ((in-image-suff
                        ((p (cons (apply (inverse g) (car x)) x)))))))
   :props (zfns-prop compose$prop phoenix$prop identity-fun$prop)))

(local
 (defthmz finite-domain-implies-finite-1
   (implies
    (and (funp f)
         (funp g)
         (subset (domain f) (image g)))
    (subset f
            (image (phoenix
                    (identity-fun (union2 (prod2 (image g) (pair 0 0))
                                          (prod2 (image g) (image f))))
                    g
                    (compose f g)))))
   :hints
   (("Goal"
     :expand
     ((subset f
              (image (phoenix
                      (identity-fun (union2 (prod2 (image g) (pair 0 0))
                                            (prod2 (image g) (image f))))
                      g
                      (compose f g)))))))
   :props (zfns-prop compose$prop phoenix$prop identity-fun$prop)))

(defthmdz finite-domain-implies-finite

; Sketch of proof.  Let g map n onto (domain f).  Extend f to domain (image g)
; by mapping (diff (image g) (domain f)) to 0; call this fx.  Then (compose fx
; g) has image that includes f, hence is finite; but this composition includes
; f, so f is finite.

  (implies (and (funp f)
                (finite (domain f)))
           (finite f))
  :hints (("Goal"
           :in-theory (disable finite-suff)
           :use ((:instance
                  finite-suff
                  (s f)
                  (f (fdif f (finite-witness (domain f))))))
           :expand ((finite (domain f)))))
  :props (zfns-prop compose$prop phoenix$prop identity-fun$prop))

(defthmz finite-iff-finite-domain
  (implies (funp f)
           (equal (finite (domain f))
                  (finite f)))
  :hints (("Goal"
           :use (finite-implies-finite-domain
                 finite-domain-implies-finite)))
  :props (zfns-prop compose$prop phoenix$prop identity-fun$prop))
