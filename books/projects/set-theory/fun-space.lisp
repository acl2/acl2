; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "base")

; Introduce the set of all functions mapping a to b, i.e., a -> b.
; Note that every such function f is a subset of the cartesian product
; (prod2 a b), hence a member of s = (powerset (prod2 a b)).
(zsub fun-space (a b)        ; name, args
      fn                     ; x
      (powerset (prod2 a b)) ; s
      (and (funp fn)
           (equal (domain fn) a))
      )

; Start proof of in-fun-space.

(defthmz subset-prod2-domain-codomain
  (implies (relation-p r)
           (subset r (prod2 (domain r)
                            (codomain r))))
  :props (zfc prod2$prop domain$prop inverse$prop)
  :hints (("Goal" :in-theory (enable subset))))

(encapsulate
  ()

  (local
   (defthmz subset-prod-2-1
     (implies (and (not (equal b 0))
                   (in x a)
                   (not (in x c)))
              (not (subset (prod2 a b) (prod2 c d))))
     :props (zfc prod2$prop domain$prop inverse$prop)
     :hints (("Goal" :restrict ((subset-necc-better-2
                                 ((a (cons x (min-in b))))))))))
  (local
   (defthmz subset-prod-2
     (implies (and (not (equal a 0))
                   (not (equal b 0))
                   (not (subset a c)))
              (not (subset (prod2 a b) (prod2 c d))))
     :props (zfc prod2$prop domain$prop inverse$prop)
     :hints (("Goal" :expand ((subset a c))))))

  (local
   (defthmz subset-prod-3-1
     (implies (and (not (equal a 0))
                   (subset a c))
              (implies (subset (prod2 a b) (prod2 c d))
                       (subset b d)))
     :props (zfc prod2$prop domain$prop inverse$prop)
     :instructions ((:bash ("Goal" :expand ((subset b d))))
                    (:casesplit (in (cons (min-in a) (subset-witness b d))
                                    (prod2 a b)))
                    :prove :prove)
     :rule-classes nil))

  (local
   (defthmz subset-prod-3-2
     (implies (and (not (equal a 0))
                   (subset a c))
              (implies (subset b d)
                       (subset (prod2 a b) (prod2 c d))))
     :hints (("Goal" :expand ((subset (prod2 a b) (prod2 c d)))))
     :props (zfc prod2$prop domain$prop inverse$prop)
     :rule-classes nil))

  (local
   (defthmz subset-prod-3
     (implies (and (not (equal a 0))
                   (subset a c))
              (equal (subset (prod2 a b) (prod2 c d))
                     (subset b d)))
     :props (zfc prod2$prop domain$prop inverse$prop)
     :hints (("Goal" :use (subset-prod-3-1 subset-prod-3-2)))))

  (defthmz subset-prod
    (equal (subset (prod2 a b) (prod2 c d))
           (or (equal a 0)
               (equal b 0)
               (and (subset a c)
                    (subset b d))))
    :props (zfc prod2$prop domain$prop inverse$prop)))

(defthmz subset-codomain
  (implies (subset r (prod2 a b))
           (subset (codomain r) b))
  :hints (("Goal"
           :in-theory (enable in-codomain-rewrite)
           :expand ((subset (codomain r) b))))
  :props (zfc prod2$prop domain$prop inverse$prop))

(defthmz in-fun-space ; alternate form of fun-space$comprehension
  (equal (in fn (fun-space a b))
         (and (funp fn)
              (equal (domain fn) a)
              (subset (codomain fn) b)))
  :props (zfc prod2$prop domain$prop inverse$prop fun-space$prop)
  :hints (("Goal"
           :restrict ((subset-transitivity
                       ((y (prod2 (domain fn) (codomain fn)))))))))

