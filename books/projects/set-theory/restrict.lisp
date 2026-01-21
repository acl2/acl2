; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "projects/set-theory/set-algebra" :dir :system)

; We introduce (restrict f s), sometimes denoted f|s.
(zsub restrict (f s) ; name, args
      p              ; x
      f              ; s
      (in (car p) s) ; u
      )

(defthmz relation-p-restrict
  (implies (relation-p f)
           (relation-p (restrict f s)))
  :props (zfc restrict$prop)
  :hints (("Goal" :expand ((relation-p (restrict f s))))))

(defthmz funp-restrict
  (implies (funp f)
           (funp (restrict f s)))
  :props (zfc restrict$prop)
  :hints (("Goal" :expand ((funp (restrict f s))))))

(defthmz domain-restrict-1
  (implies (in x (domain (restrict f s)))
           (in x (domain f)))
  :hints (("Goal" :in-theory (e/d (in-domain-rewrite)
                                  (in-cons-apply))))
  :props (zfc restrict$prop domain$prop))

(defthmz domain-restrict-2
  (implies (in x (domain (restrict f s)))
           (in x s))
  :hints (("Goal" :in-theory (e/d (in-domain-rewrite)
                                  (in-cons-apply))))
  :props (zfc restrict$prop domain$prop))

(defthmz domain-restrict-3
  (implies (and (in x (domain f))
                (in x s))
           (in x (domain (restrict f s))))
  :hints (("Goal"
           :restrict ((in-car-domain-alt
                       ((p (cons x (apply f x))))))
           :in-theory (e/d (in-domain-rewrite)
                           (in-cons-apply))))
  :props (zfc restrict$prop domain$prop))

(defthmz domain-restrict
  (equal (domain (restrict f s))
         (int2 (domain f) s))
  :props (zfc restrict$prop domain$prop diff$prop)
  :hints (("Goal"
           :in-theory (enable extensionality-rewrite subset))))

(defthmz apply-restrict
  (implies (and (funp f)
                (force (subset x (domain f)))
                (force (in a x)))
           (equal (apply (restrict f x) a)
                  (apply f a)))
  :props (zfc domain$prop restrict$prop diff$prop)
  :hints (("Goal" :in-theory (enable apply-intro))))

(defthmz restrict-union2
  (implies (and (relation-p r1)
                (relation-p r2))
           (equal (restrict (union2 r1 r2) s)
                  (union2 (restrict r1 s)
                          (restrict r2 s))))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc restrict$prop))

(defthmz restrict-domain
  (implies (relation-p r)
           (equal (restrict r (domain r))
                  r))
  :hints (("Goal" :in-theory (enable extensionality-rewrite)))
  :props (zfc domain$prop restrict$prop))

(local (defthmz restrict-pair-is-0-lemma
         (implies (and (not (in a1 s))
                       (not (in a2 s)))
                  (subset (restrict (pair (cons a1 b1)
                                          (cons a2 b2))
                                    s)
                          0))
         :hints (("Goal" :in-theory (e/d (subset)
                                         (subset-x-0))))
         :props (zfc restrict$prop)
         :rule-classes nil))

(defthmz restrict-pair-is-0
  (implies (and (not (in a1 s))
                (not (in a2 s)))
           (equal (restrict (pair (cons a1 b1)
                                  (cons a2 b2))
                            s)
                  0))
  :hints (("Goal" :use restrict-pair-is-0-lemma))
  :props (zfc restrict$prop))

(defthmz image-restrict-1
  (implies (in a (image (restrict fn s)))
           (in a (image fn)))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop)
  :hints (("Goal"
           :restrict ((in-image-suff
                       ((p (cons (apply (inverse (restrict fn s)) a)
                                 a)))))
           :use ((:instance in-image-rewrite (x a)
                            (r (restrict fn s)))))))

(defthmz image-restrict
  (subset (image (restrict fn s))
          (image fn))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop)
  :hints (("Goal" :in-theory (enable subset))))

(defthmz image-restrict-alt

; This is a version of image-restrict that builds in transitivity of subset, so
; as to avoid free variables.

  (implies (and (funp fn)
                (subset (image fn) s))
           (subset (image (restrict fn dom)) s))
  :props (zfc prod2$prop domain$prop inverse$prop restrict$prop)
  :hints (("Goal" :restrict ((subset-transitivity ((y (image fn))))))))

(defthmz restrict-to-0-subset-version
  (subset (restrict fn 0)
          0)
  :hints (("Goal" :in-theory (e/d (subset) (subset-x-0))))
  :props (restrict$prop)
  :rule-classes nil)

(defthmz restrict-to-0
  (equal (restrict fn 0)
         0)
  :hints (("Goal" :use restrict-to-0-subset-version))
  :props (zfc restrict$prop))
